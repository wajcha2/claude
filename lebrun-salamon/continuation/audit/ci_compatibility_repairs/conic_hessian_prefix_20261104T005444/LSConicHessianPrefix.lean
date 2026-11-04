import LSTangentComparison
import LSHamiltonianJets
import LSContactVelocityTarget
import LSIntrinsicVelocity

/-!
# The full conic family's quadratic diagonal symbol

The generic input concerns only first-jet restriction of the complete
represented Hom functor. All contact coefficients and diagonal symbols
are computed from the actual scheme maps and their existing normalized
local pullback comparisons.
-/

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

namespace LeBrunSalamon.StandardInputs

/-- The classical first-jet restriction theorem for 2p, normalized to
this actual source dual-number lift and the existing universal velocity
morphism. Kollár, Rational Curves on Algebraic Varieties II.3.5;
Araujo--Kollár, Rational Curves on Varieties, Remark 9 (2003), p.7 of
arXiv:math/0203173. Root independently approved the exact maps/type. -/
theorem homOpen_sourceFirstJet_dominant (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {d : ℕ} (X : SmoothProperComplexVariety d)
    (H : HomSpacePresentation P X) (x : ComplexPoint X)
    (tau : HomFirstJet.SourceLift P p)
    (htau : tau.map ≠ Infinitesimal.dualToC ≫ p.map)
    (C : GlobalVelocity.TargetChart X x)
    (V : (FixedNodeHom.parameter P p H x).Opens)
    (t : PointsOver ComplexBase (𝟙 ComplexBase) V.toScheme
      (V.ι ≫ FixedNodeHom.toC P p H x))
    (f : RationalCurve P X)
    (hf : f.map = HomDeformation.curveAt P H p x
      ⟨t.val ≫ V.ι, by simpa only [Category.assoc] using t.property⟩)
    (hfree : IsVeryFreeRationalCurve P X (intrinsicTangentBundle X) f) :
    DenseRange (V.ι ≫ GlobalVelocity.homVelocity P p H x tau C).base := by
  sorry

end LeBrunSalamon.StandardInputs

namespace LeBrunSalamon.Refinement.Jets.PointFrame

/-- The actual coefficient at the target point agrees with evaluation
of the actual pulled coefficient on any smaller source neighborhood.
The fiber-composition map is the original canonical pullback comparison. -/
theorem lineFiberCoefficient_composition {d : ℕ} {X : SmoothProperComplexVariety d}
    {L : LineBundle X.scheme} {x : ComplexPoint X} (F : PointFrame X L x)
    {Y : Scheme} (f : Y ⟶ X.scheme) (p : ComplexBase ⟶ Y)
    (hx : p ≫ f = x.map) (V : Y.Opens)
    (hV : V ≤ f ⁻¹ᵁ F.frame.openSet) (hp : ⊤ ≤ p ⁻¹ᵁ V)
    (a : SectionsOn (pullbackModule f L.sheaf) V) :
    F.lineFiberCoefficient
      (fiberComposition f p x.map hx L.sheaf
        (PositiveFrame.localFiberValue p (pullbackModule f L.sheaf) V hp a)) =
      p.appLE V ⊤ hp (LocalFrameJetProof.coefficientOn F.frame f V hV a) := by
  let e := LocalFrameJetProof.coefficientOn F.frame f V hV
  let b : SectionsOn (pullbackModule f L.sheaf) V :=
    (pullbackModule f L.sheaf).presheaf.map (homOfLE hV).op
      (pullLocalSection f L.sheaf F.frame.openSet (F.frame.coefficient.symm 1))
  have hb : e b = 1 := by
    change LocalFrameJetProof.coefficientOn F.frame f V hV
      ((pullbackModule f L.sheaf).presheaf.map (homOfLE hV).op
        (pullLocalSection f L.sheaf F.frame.openSet (F.frame.coefficient.symm 1))) = 1
    rw [LocalFrameJetProof.coefficientOn_local, map_one]
  have ha : a = e a • b := by
    apply e.injective
    rw [e.map_smul, hb]
    exact (mul_one (e a)).symm
  have hpU : ⊤ ≤ p ⁻¹ᵁ (f ⁻¹ᵁ F.frame.openSet) :=
    hp.trans (p.preimage_mono hV)
  have hframe : F.lineFiberCoefficient
      (fiberComposition f p x.map hx L.sheaf
        (PositiveFrame.localFiberValue p (pullbackModule f L.sheaf) V hp b)) = 1 := by
    dsimp only [b]
    rw [SourceTangent.localFiberValue_restrict p (pullbackModule f L.sheaf)
      hV hp hpU,
      SourceTangent.localFiberValue_composition f p x.map hx L.sheaf F.frame.openSet
        hpU F.pointSupport,
      F.lineFiberCoefficient_local, map_one]
  have hscale (r : RingSections Y V)
      (z : SectionsOn (pullbackModule f L.sheaf) V) :
      F.lineFiberCoefficient
        (fiberComposition f p x.map hx L.sheaf
          (PositiveFrame.localFiberValue p (pullbackModule f L.sheaf) V hp (r • z))) =
      p.appLE V ⊤ hp r * F.lineFiberCoefficient
        (fiberComposition f p x.map hx L.sheaf
          (PositiveFrame.localFiberValue p (pullbackModule f L.sheaf) V hp z)) := by
    change F.lineFiberCoefficient
      ((compositionPullback p f x.map hx L.sheaf).hom.app ⊤
        ((pullbackModule p (pullbackModule f L.sheaf)).val.map (homOfLE hp).op
          (pullLocalSection p (pullbackModule f L.sheaf) V (r • z)))) = _
    rw [PullbackPairProof.pullLocalSection_smul,
      (pullbackModule p (pullbackModule f L.sheaf)).val.map_smul,
      Scheme.Modules.Hom.app_smul, F.lineFiberCoefficient.map_smul] <;> rfl
  calc
    _ = F.lineFiberCoefficient
        (fiberComposition f p x.map hx L.sheaf
          (PositiveFrame.localFiberValue p (pullbackModule f L.sheaf) V hp (e a • b))) :=
      congrArg (fun z => F.lineFiberCoefficient
        (fiberComposition f p x.map hx L.sheaf
          (PositiveFrame.localFiberValue p (pullbackModule f L.sheaf) V hp z))) ha
    _ = p.appLE V ⊤ hp (e a) * F.lineFiberCoefficient
        (fiberComposition f p x.map hx L.sheaf
          (PositiveFrame.localFiberValue p (pullbackModule f L.sheaf) V hp b)) :=
      hscale (e a) b
    _ = p.appLE V ⊤ hp (e a) := by rw [hframe, mul_one]

end LeBrunSalamon.Refinement.Jets.PointFrame

namespace LeBrunSalamon.Refinement.ConicJetProof.SourceMixedSymbol

open Core.ExternalTensorCoordinates

/-- A target-line frame on precisely the source frame's affine open. -/
abbrev frameOn {Y : Scheme} {L M : LineBundle Y} (S : AffineLineFrame L)
    (m : SectionsOn M.sheaf S.openSet ≃ₗ[RingSections Y S.openSet]
      RingSections Y S.openSet) : AffineLineFrame M where
  openSet := S.openSet
  isAffine := S.isAffine
  coefficient := m

def multiplier {Y : Scheme} {L M : LineBundle Y}
    (q : L.sheaf ⟶ M.sheaf) (S : AffineLineFrame L)
    (m : SectionsOn M.sheaf S.openSet ≃ₗ[RingSections Y S.openSet]
      RingSections Y S.openSet) : RingSections Y S.openSet :=
  m (q.app S.openSet (S.coefficient.symm 1))

/-- The coefficient of a genuine line morphism is multiplication by
its value on the actual supplied local frame. It need not be a unit. -/
theorem coefficient_map {Y : Scheme} {L M : LineBundle Y}
    (q : L.sheaf ⟶ M.sheaf) (S : AffineLineFrame L)
    (m : SectionsOn M.sheaf S.openSet ≃ₗ[RingSections Y S.openSet]
      RingSections Y S.openSet) (a : SectionsOn L.sheaf S.openSet) :
    m (q.app S.openSet a) = multiplier q S m * S.coefficient a := by
  have ha : a = S.coefficient a • S.coefficient.symm 1 := by
    rw [← S.coefficient.symm.map_smul]
    simpa only [smul_eq_mul, mul_one] using (S.coefficient.symm_apply_apply a).symm
  calc
    _ = m (q.app S.openSet (S.coefficient a • S.coefficient.symm 1)) :=
      congrArg (fun z => m (q.app S.openSet z)) ha
    _ = S.coefficient a * multiplier q S m := by
      rw [Scheme.Modules.Hom.app_smul, m.map_smul] <;> rfl
    _ = multiplier q S m * S.coefficient a := mul_comm _ _

theorem localCoefficient_postcompose {Y : Scheme} {L M : LineBundle Y}
    (q : L.sheaf ⟶ M.sheaf) (S : AffineLineFrame L)
    (m : SectionsOn M.sheaf S.openSet ≃ₗ[RingSections Y S.openSet]
      RingSections Y S.openSet) (a : AlgebraicSection L.sheaf) :
    (frameOn S m).localCoefficient (a ≫ q) =
      multiplier q S m * S.localCoefficient a :=
  coefficient_map q S m (Scheme.Modules.Hom.app a S.openSet (1 : RingSections Y S.openSet))

/-- Push the actual finite source expansion through the same line
morphism in both tensor factors. -/
def mappedExpansion {d : ℕ} {Y : SmoothProperComplexVariety d}
    {L M : LineBundle Y.scheme} {B : ExternalSquareSections Y L}
    (E : ExternalExpansion Y L B) (q : L.sheaf ⟶ M.sheaf) :
    ExternalExpansion Y M (B ≫ externalTensorMap Y.structureMap q q) where
  size := E.size
  left i := E.left i ≫ q
  right i := E.right i ≫ q
  equation := by
    conv_lhs => rw [E.equation]
    rw [Preadditive.sum_comp]
    apply Finset.sum_congr rfl
    intro i hi
    exact CurveExchangeProof.externalTensorMap_product Y.structureMap L M q
      (E.left i) (E.right i)

theorem mapped_orderTwo {d : ℕ} {Y : SmoothProperComplexVariety d}
    {L M : LineBundle Y.scheme} {B : ExternalSquareSections Y L}
    (q : L.sheaf ⟶ M.sheaf)
    (hB : VanishesQuadraticallyAlongDiagonal Y.structureMap
      (externalSquareLine Y.structureMap L).sheaf B) :
    VanishesQuadraticallyAlongDiagonal Y.structureMap
      (externalSquareLine Y.structureMap M).sheaf
        (B ≫ externalTensorMap Y.structureMap q q) := by
  change (Scheme.Modules.pullback (diagonalPowerInclusion Y.structureMap 2)).map
    (B ≫ externalTensorMap Y.structureMap q q) = 0
  rw [Functor.map_comp]
  change restrictSection (diagonalPowerInclusion Y.structureMap 2) B ≫ _ = 0
  rw [hB, zero_comp]

/-- Full Leibniz expansion of the mapped undivided Hessian. The lower
symbols are retained here, so the subsequent cancellations are explicit. -/
theorem mapped_secondSlotSecond {d : ℕ} {Y : SmoothProperComplexVariety d}
    {L M : LineBundle Y.scheme} {B : ExternalSquareSections Y L}
    (E : ExternalExpansion Y L B) (q : L.sheaf ⟶ M.sheaf)
    (S : AffineLineFrame L)
    (m : SectionsOn M.sheaf S.openSet ≃ₗ[RingSections Y.scheme S.openSet]
      RingSections Y.scheme S.openSet)
    (u : SectionsOn (tangentSheaf Y.structureMap) S.openSet) :
    (mappedExpansion E q).secondSlotSecond (frameOn S m) u u =
      multiplier q S m * tangentActs Y.structureMap S.openSet u
        (tangentActs Y.structureMap S.openSet u (multiplier q S m)) * E.diagonalValue S +
      (2 * multiplier q S m * tangentActs Y.structureMap S.openSet u (multiplier q S m)) *
        E.secondSlotFirst S u +
      (multiplier q S m)^2 * E.secondSlotSecond S u u := by
  let D : RingSections Y.scheme S.openSet → RingSections Y.scheme S.openSet :=
    tangentActs Y.structureMap S.openSet u
  change (∑ i, (frameOn S m).localCoefficient (E.left i ≫ q) *
    D (D ((frameOn S m).localCoefficient (E.right i ≫ q)))) = _
  simp_rw [localCoefficient_postcompose]
  change (∑ i, (multiplier q S m * S.localCoefficient (E.left i)) *
      D (D (multiplier q S m * S.localCoefficient (E.right i)))) =
    (multiplier q S m * D (D (multiplier q S m))) *
      (∑ i, S.localCoefficient (E.left i) * S.localCoefficient (E.right i)) +
    (2 * multiplier q S m * D (multiplier q S m)) *
      (∑ i, S.localCoefficient (E.left i) * D (S.localCoefficient (E.right i))) +
    (multiplier q S m)^2 *
      (∑ i, S.localCoefficient (E.left i) * D (D (S.localCoefficient (E.right i))))
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [D, tangentActs_leibniz, tangentActs_add_function]
  ring

/-- Assemble the three properties of the original source bivector from
its proved existence and uniqueness theorem. -/
def sourceKernel (P : ProjectiveLineOverC) :
    NormalizedContactKernel (n := 0) (projectiveLineVariety P) (identityCurveContact P) where
  twoPointSection := sourceBivector P
  symmetric := (Classical.choose_spec (sourceBivector_existsUnique P)).1.1
  orderTwo := (Classical.choose_spec (sourceBivector_existsUnique P)).1.2.1
  normalized := (Classical.choose_spec (sourceBivector_existsUnique P)).1.2.2

/-- The actual source identity has mixed coefficient -2 times the
square of the line-morphism value. All acceleration terms have vanished
by the independently proved value and first-symbol equations. -/
theorem mapped_source_mixed (P : ProjectiveLineOverC) (M : LineBundle ProjectiveLine)
    (q : tangentSheaf P.structureMap ⟶ M.sheaf)
    (S : AffineLineFrame (identityCurveContact P).sequence.line)
    (m : SectionsOn M.sheaf S.openSet ≃ₗ[RingSections ProjectiveLine S.openSet]
      RingSections ProjectiveLine S.openSet)
    (u : SectionsOn (tangentSheaf P.structureMap) S.openSet) :
    (mappedExpansion (sourceKernel P).expansion q).mixedSecond (frameOn S m) u u =
      -2 * (m (q.app S.openSet u))^2 := by
  let K := sourceKernel P
  let E := K.expansion
  have htwo := mapped_orderTwo (M := M) q K.orderTwo
  have hh : (mappedExpansion E q).secondSlotSecond (frameOn S m) u u =
      2 * (m (q.app S.openSet u))^2 := by
    rw [mapped_secondSlotSecond, E.diagonalValue_zero_of_orderTwo K.orderTwo,
      E.secondSlotFirst_zero_of_orderTwo K.orderTwo]
    simp only [mul_zero, zero_add]
    have hn := K.expansion_normalized S u u
    rw [hn]
    change (multiplier q S m)^2 *
      (2 * S.coefficient u * S.coefficient u) = 2 * (m (q.app S.openSet u))^2
    rw [coefficient_map q S m u]
    ring
  change (mappedExpansion E q).mixedSecond (frameOn S m) u u = _
  rw [(mappedExpansion E q).mixedSecond_eq_neg_of_orderTwo htwo (frameOn S m) u u, hh]
  ring

/-- The actual curve identity holds for every expansion, by the existing
canonical tensor pullback comparison and its invertibility. -/
theorem curveIdentity_expansion (P : ProjectiveLineOverC) {n : ℕ}
    {X : SmoothProperComplexVariety (2*n+1)} (C : IntrinsicContactStructure X)
    (f : RationalCurve P X) (B : ExternalSquareSections X C.sequence.line)
    (h : CurveKernelIdentity P C f B) (E : ExternalExpansion X C.sequence.line B) :
    (∑ i, externalProductSection P.structureMap
      (pullSection f.map (E.left i)) (pullSection f.map (E.right i))) =
      sourceBivector P ≫ externalTensorMap P.structureMap
        (curveContactVelocity P C f) (curveContactVelocity P C f) := by
  let q := curveExternalComparison P f C.sequence.line.sheaf C.sequence.line.sheaf
  letI : IsIso q := curveExternalComparison_isIso P f
    C.sequence.line.sheaf C.sequence.line.sheaf
  apply (cancel_mono q).mp
  have hs : (∑ i, externalProductSection P.structureMap
      (pullSection f.map (E.left i)) (pullSection f.map (E.right i))) ≫ q =
      pullSection (curveSquareMap P f) B := by
    dsimp only [q]
    rw [Preadditive.sum_comp]
    simp_rw [curveExternalComparison_onProducts]
    have he := congrArg (fun a : ExternalSquareSections X C.sequence.line =>
      pullSection (curveSquareMap P f) a) E.equation
    simpa only [pullSection, restrictSection, Functor.map_sum, Preadditive.comp_sum] using he.symm
  rw [hs]
  simpa only [sourceContactValue, q, Category.assoc] using
    (curveKernelIdentity_iff P C f B).mp h

def pulledExpansion (P : ProjectiveLineOverC) {n : ℕ}
    {X : SmoothProperComplexVariety (2*n+1)} (C : IntrinsicContactStructure X)
    (f : RationalCurve P X) (B : ExternalSquareSections X C.sequence.line)
    (h : CurveKernelIdentity P C f B) (E : ExternalExpansion X C.sequence.line B) :
    ExternalExpansion (projectiveLineVariety P) (pullbackBundle f.map C.sequence.line)
      (sourceBivector P ≫ externalTensorMap P.structureMap
        (curveContactVelocity P C f) (curveContactVelocity P C f)) where
  size := E.size
  left i := pullSection f.map (E.left i)
  right i := pullSection f.map (E.right i)
  equation := (curveIdentity_expansion P C f B h E).symm

/-- The finite mixed derivative sum for ANY target expansion is forced by
the actual source-curve section identity. The displayed coefficient frame
can be `coefficientOn` of any target affine frame. -/
theorem source_curve_mixed (P : ProjectiveLineOverC) {n : ℕ}
    {X : SmoothProperComplexVariety (2*n+1)} (C : IntrinsicContactStructure X)
    (f : RationalCurve P X) (B : ExternalSquareSections X C.sequence.line)
    (h : CurveKernelIdentity P C f B) (E : ExternalExpansion X C.sequence.line B)
    (S : AffineLineFrame (identityCurveContact P).sequence.line)
    (m : SectionsOn (pullbackModule f.map C.sequence.line.sheaf) S.openSet ≃ₗ[
      RingSections ProjectiveLine S.openSet] RingSections ProjectiveLine S.openSet)
    (u : SectionsOn (tangentSheaf P.structureMap) S.openSet) :
    (∑ i, tangentActs P.structureMap S.openSet u
        ((frameOn (M := pullbackBundle f.map C.sequence.line) S m).localCoefficient
          (pullSection f.map (E.left i))) *
      tangentActs P.structureMap S.openSet u
        ((frameOn (M := pullbackBundle f.map C.sequence.line) S m).localCoefficient
          (pullSection f.map (E.right i)))) =
      -2 * (m ((curveContactVelocity P C f).app S.openSet u))^2 := by
  let EP := pulledExpansion P C f B h E
  let ES := mappedExpansion (M := pullbackBundle f.map C.sequence.line)
    (sourceKernel P).expansion (curveContactVelocity P C f)
  let F := frameOn (M := pullbackBundle f.map C.sequence.line) S m
  have htwo := mapped_orderTwo (M := pullbackBundle f.map C.sequence.line)
    (curveContactVelocity P C f) (sourceKernel P).orderTwo
  change EP.mixedSecond F u u = _
  calc
    _ = -EP.secondSlotSecond F u u := EP.mixedSecond_eq_neg_of_orderTwo htwo F u u
    _ = -ES.secondSlotSecond F u u := congrArg Neg.neg
      (EP.secondSlotSecond_independent ES F u u)
    _ = ES.mixedSecond F u u := (ES.mixedSecond_eq_neg_of_orderTwo htwo F u u).symm
    _ = -2 * (m ((curveContactVelocity P C f).app S.openSet u))^2 :=
      mapped_source_mixed P (pullbackBundle f.map C.sequence.line)
        (curveContactVelocity P C f) S m u

end LeBrunSalamon.Refinement.ConicJetProof.SourceMixedSymbol

namespace LeBrunSalamon.Refinement

namespace ConicJetProof

/-- A line bundle can be framed on an affine neighborhood inside any
specified neighborhood of its point. The frame is a restriction of the
original locally free trivialization. -/
theorem affineLineFrame_inside {Y : Scheme} (L : LineBundle Y)
    (y : Y) (U : Y.Opens) (hy : y ∈ U) :
    ∃ F : AffineLineFrame L, y ∈ F.openSet ∧ F.openSet ≤ U := by
  classical
  obtain ⟨q, hq, hr⟩ := L.locallyFree
  letI := hq
  obtain ⟨i, hyi⟩ :=
    ((_root_.Opens.coversTop_iff Y q.X).mp q.coversTop).exists_mem y
  obtain ⟨V, hV, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (X := Y) (x := y) (U := U ⊓ q.X i) ⟨hy, hyi⟩
  let e : L.sheaf.over V ≅ SheafOfModules.unit (Y.ringCatSheaf.over V) :=
    (SheafTensor.freeTrivializationRestrict (homOfLE (le_trans hVU inf_le_right))
      (SheafTensor.localBasisTrivialization q hr i)).symm ≪≫
    coproductUniqueIso (fun _ : Fin 1 => SheafOfModules.unit (Y.ringCatSheaf.over V))
  let eΓ := ((SheafOfModules.evaluation (Y.ringCatSheaf.over V)
    (op (Over.mk (𝟙 V)))).mapIso e).toLinearEquiv
  exact ⟨⟨V, hV, eΓ⟩, hyV, le_trans hVU inf_le_left⟩

theorem pointFrame_inside {d : ℕ} (Y : SmoothProperComplexVariety d)
    (L : LineBundle Y.scheme) (y : ComplexPoint Y) (U : Y.scheme.Opens)
    (hy : ⊤ ≤ y.map ⁻¹ᵁ U) :
    ∃ F : PointFrame Y L y, F.frame.openSet ≤ U := by
  let z : ComplexBase := IsLocalRing.closedPoint ℂ
  obtain ⟨F, hyF, hFU⟩ := affineLineFrame_inside L (y.map z) U (hy trivial)
  have hr : Set.range y.map ⊆ Set.range F.openSet.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    change y.map w ∈ F.openSet
    rw [Subsingleton.elim w z]
    exact hyF
  exact ⟨⟨F, IsOpenImmersion.lift F.openSet.ι y.map hr,
    IsOpenImmersion.lift_fac _ _ _⟩, hFU⟩

/-- A constant actual dual point has zero original tangent vector. -/
theorem pointVector_zero_of_constant {d : ℕ} (Y : SmoothProperComplexVariety d)
    (y : ComplexPoint Y)
    (tau : Infinitesimal.PointLift Y.scheme Y.structureMap ⟨y.map, y.overC⟩)
    (h : tau.map = Infinitesimal.dualToC ≫ y.map) :
    SourceTangent.pointVector Y y tau = 0 := by
  have hc : SourceTangent.pointDeformation tau = FamilyVariation.constant y.map y.overC := by
    apply FamilyVariation.Deformation.ext
    change DualThickening.parameter (𝟙 ComplexBase) ≫ tau.map =
      DualThickening.projection (𝟙 ComplexBase) ≫ y.map
    rw [h, ← Category.assoc, DualThickening.parameter_overC]
    simp only [DualThickening.toC, Category.comp_id]
  change (SourceTangent.pointDeformation tau).variation Y = 0
  rw [hc, FamilyVariation.constant_variation]

/-- The actual projective source has a nonconstant dual-number lift at
every complex point. Its vector is taken in the original rank-one tangent
fiber and realized by the canonical affine tangent comparison. -/
theorem sourceLift_nonconstant (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) :
    ∃ tau : HomFirstJet.SourceLift P p,
      tau.map ≠ Infinitesimal.dualToC ≫ p.map := by
  let y : ComplexPoint (projectiveLineVariety P) := ⟨p.map, p.overC⟩
  letI : FiniteDimensional ℂ (TangentFiber (projectiveLineVariety P) y) :=
    fiber_finite (intrinsicTangentBundle (projectiveLineVariety P)) p.map
  have hd : Module.finrank ℂ (TangentFiber (projectiveLineVariety P) y) = 1 :=
    fiber_dimension (intrinsicTangentBundle (projectiveLineVariety P)) p.map
  have hn : Nontrivial (TangentFiber (projectiveLineVariety P) y) :=
    Module.nontrivial_of_finrank_pos (R := ℂ)
      (M := TangentFiber (projectiveLineVariety P) y) (by omega)
  letI := hn
  obtain ⟨v, hv⟩ := exists_ne (0 : TangentFiber (projectiveLineVariety P) y)
  obtain ⟨C⟩ := GlobalVelocity.targetChart_exists (projectiveLineVariety P) y
  obtain ⟨tau, htau⟩ := IntrinsicTangent.pointVector_surjective C v
  refine ⟨tau, ?_⟩
  intro h
  exact hv (htau.symm.trans (pointVector_zero_of_constant _ y tau h))

namespace ActualHomVelocity

open FamilyVariation

variable (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
  {d : ℕ} {X : SmoothProperComplexVariety d}
  (H : HomSpacePresentation P X) (x : ComplexPoint X)
  (tau : HomFirstJet.SourceLift P p)

def targetLift
    (t : PointsOver ComplexBase (𝟙 ComplexBase)
      (FixedNodeHom.parameter P p H x) (FixedNodeHom.toC P p H x)) :
    Infinitesimal.PointLift X.scheme X.structureMap ⟨x.map, x.overC⟩ :=
  Charts.AffineTangentLift.push (HomDeformation.curveAt P H p x t)
    (HomDeformation.curveAt_overC P H p x t)
    (HomDeformation.curveAt_marking P H p x t) tau

theorem firstJet_atPoint
    (t : PointsOver ComplexBase (𝟙 ComplexBase)
      (FixedNodeHom.parameter P p H x) (FixedNodeHom.toC P p H x)) :
    GlobalVelocity.recenter
      ((HomFirstJet.deformation P p H x tau).pullback t.val t.property)
      (by rw [← Category.assoc, t.property]) =
        HomVelocityValue.pointFamily (targetLift P p H x tau t) := by
  apply Deformation.ext
  exact HomFirstJet.deformation_atPoint P p H x tau t

def value (C : GlobalVelocity.TargetChart X x)
    (t : PointsOver ComplexBase (𝟙 ComplexBase)
      (FixedNodeHom.parameter P p H x) (FixedNodeHom.toC P p H x)) :
    Infinitesimal.Tangent C.Ring C.evaluation :=
  HomVelocityValue.tangentValue C.evaluation
    (t.val ≫ GlobalVelocity.homVelocity P p H x tau C)
    (by rw [Category.assoc, GlobalVelocity.homVelocity_overC, t.property])

theorem value_eq_chartEvaluation (C : GlobalVelocity.TargetChart X x)
    (t : PointsOver ComplexBase (𝟙 ComplexBase)
      (FixedNodeHom.parameter P p H x) (FixedNodeHom.toC P p H x)) :
    value P p H x tau C t = IntrinsicTangent.chartEvaluation C
      (SourceTangent.pointVector X x (targetLift P p H x tau t)) := by
  have h : value P p H x tau C t =
      HomVelocityValue.pointValue C (targetLift P p H x tau t) := by
    apply HomVelocityValue.tangentValue_congr
    rw [GlobalVelocity.homVelocity_parameterChange, firstJet_atPoint]
  rw [h, HomVelocityValue.pointValue_eq_chartEvaluation]

theorem value_eq_pointDifferential (C : GlobalVelocity.TargetChart X x)
    (t : PointsOver ComplexBase (𝟙 ComplexBase)
      (FixedNodeHom.parameter P p H x) (FixedNodeHom.toC P p H x)) :
    value P p H x tau C t = IntrinsicTangent.chartEquivalence C
      (SourceTangent.pointDifferential (projectiveLineVariety P) X
        (HomDeformation.curveAt P H p x t) (HomDeformation.curveAt_overC P H p x t)
        ⟨p.map, p.overC⟩ x (HomDeformation.curveAt_marking P H p x t)
        (SourceTangent.pointVector (projectiveLineVariety P) ⟨p.map, p.overC⟩ tau)) := by
  rw [value_eq_chartEvaluation]
  exact congrArg (IntrinsicTangent.chartEvaluation C)
    (SourceTangent.pointVector_push (projectiveLineVariety P) X
      (HomDeformation.curveAt P H p x t) (HomDeformation.curveAt_overC P H p x t)
      ⟨p.map, p.overC⟩ x (HomDeformation.curveAt_marking P H p x t) tau)

end ActualHomVelocity

namespace FixedNeighborhood

variable (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
  {d : ℕ} {X : SmoothProperComplexVariety d}
  (H : HomSpacePresentation P X) (x : ComplexPoint X) (U : H.parameter.Opens)

def openSet : (FixedNodeHom.parameter P p H x).Opens :=
  FixedNodeHom.inclusion P p H x ⁻¹ᵁ U

def toOpen : (openSet P p H x U).toScheme ⟶ U.toScheme :=
  (FixedNodeHom.inclusion P p H x).resLE U (openSet P p H x U) le_rfl

theorem toOpen_inclusion :
    toOpen P p H x U ≫ U.ι =
      (openSet P p H x U).ι ≫ FixedNodeHom.inclusion P p H x :=
  Scheme.Hom.resLE_comp_ι _ _

theorem toOpen_overC :
    toOpen P p H x U ≫ (U.ι ≫ H.toC) =
      (openSet P p H x U).ι ≫ FixedNodeHom.toC P p H x := by
  rw [← Category.assoc, toOpen_inclusion, Category.assoc,
    FixedNodeHom.inclusion_overC]

theorem locallyOfFiniteType (hU : Smooth (U.ι ≫ H.toC)) :
    LocallyOfFiniteType ((openSet P p H x U).ι ≫ FixedNodeHom.toC P p H x) := by
  letI : IsClosedImmersion x.map := FatPointOpenFactorizationProof.complexPoint_isClosedImmersion x
  letI : LocallyOfFiniteType (FixedNodeHom.inclusion P p H x) := by
    change LocallyOfFiniteType (pullback.fst (FixedNodeHom.markedEvaluation P p H) x.map)
    infer_instance
  letI : Smooth (U.ι ≫ H.toC) := hU
  haveI : LocallyOfFiniteType (toOpen P p H x U) := by
    dsimp only [toOpen]
    infer_instance
  rw [← toOpen_overC]
  infer_instance

def fixedPoint
    (t : PointsOver ComplexBase (𝟙 ComplexBase) (openSet P p H x U).toScheme
      ((openSet P p H x U).ι ≫ FixedNodeHom.toC P p H x)) :
    PointsOver ComplexBase (𝟙 ComplexBase)
      (FixedNodeHom.parameter P p H x) (FixedNodeHom.toC P p H x) :=
  ⟨t.val ≫ (openSet P p H x U).ι, by
    simpa only [Category.assoc] using t.property⟩

def familyPoint
    (t : PointsOver ComplexBase (𝟙 ComplexBase) (openSet P p H x U).toScheme
      ((openSet P p H x U).ι ≫ FixedNodeHom.toC P p H x)) :
    PointsOver ComplexBase (𝟙 ComplexBase) U.toScheme (U.ι ≫ H.toC) :=
  ⟨t.val ≫ toOpen P p H x U, by rw [Category.assoc, toOpen_overC, t.property]⟩

theorem forget_fixedPoint
    (t : PointsOver ComplexBase (𝟙 ComplexBase) (openSet P p H x U).toScheme
      ((openSet P p H x U).ι ≫ FixedNodeHom.toC P p H x)) :
    FixedNodeHom.forget P p H x (fixedPoint P p H x U t) =
      HomTwoPointEvaluation.parameterPoint P H U (familyPoint P p H x U t) := by
  apply Subtype.ext
  change (t.val ≫ (openSet P p H x U).ι) ≫ FixedNodeHom.inclusion P p H x =
    (t.val ≫ toOpen P p H x U) ≫ U.ι
  simp only [Category.assoc, toOpen_inclusion]

theorem curveAt_forget
    (t : PointsOver ComplexBase (𝟙 ComplexBase)
      (FixedNodeHom.parameter P p H x) (FixedNodeHom.toC P p H x)) :
    HomDeformation.curveAt P H p x t =
      H.mapAt P (FixedNodeHom.forget P p H x t) := by
  unfold HomDeformation.curveAt FixedNodeHom.evaluation
  rw [← Category.assoc, HomDeformation.sourceAtPoint_naturality]
  rfl

theorem curveAt_fixedPoint
    (t : PointsOver ComplexBase (𝟙 ComplexBase) (openSet P p H x U).toScheme
      ((openSet P p H x U).ι ≫ FixedNodeHom.toC P p H x)) :
    HomDeformation.curveAt P H p x (fixedPoint P p H x U t) =
      H.mapAt P (HomTwoPointEvaluation.parameterPoint P H U (familyPoint P p H x U t)) := by
  rw [curveAt_forget, forget_fixedPoint]

/-- A curve in the original Hom open whose marked point is x gives a
point of the actual fixed-node fiber open. -/
theorem point_exists
    (t : PointsOver ComplexBase (𝟙 ComplexBase) U.toScheme (U.ι ≫ H.toC))
    (f : RationalCurve P X)
    (hf : f.map = H.mapAt P (HomTwoPointEvaluation.parameterPoint P H U t))
    (hx : p.map ≫ f.map = x.map) :
    ∃ q : PointsOver ComplexBase (𝟙 ComplexBase) (openSet P p H x U).toScheme
      ((openSet P p H x U).ι ≫ FixedNodeHom.toC P p H x),
      f.map = HomDeformation.curveAt P H p x (fixedPoint P p H x U q) := by
  let tH := HomTwoPointEvaluation.parameterPoint P H U t
  have htH : tH.val ≫ FixedNodeHom.markedEvaluation P p H = (𝟙 ComplexBase) ≫ x.map := by
    rw [← HomDeformation.mapAt_markedEvaluation, ← hf, hx, Category.id_comp]
  let tF := FixedNodeHom.lift P p H x tH htH
  have hforget : tF.val ≫ FixedNodeHom.inclusion P p H x = t.val ≫ U.ι :=
    FixedNodeHom.lift_inclusion P p H x tH htH
  have hr : Set.range tF.val ⊆ Set.range (openSet P p H x U).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    change (tF.val ≫ FixedNodeHom.inclusion P p H x) z ∈ U
    rw [hforget]
    exact (t.val z).property
  let qmap := IsOpenImmersion.lift (openSet P p H x U).ι tF.val hr
  have hq : qmap ≫ (openSet P p H x U).ι = tF.val :=
    IsOpenImmersion.lift_fac _ _ _
  let q : PointsOver ComplexBase (𝟙 ComplexBase) (openSet P p H x U).toScheme
      ((openSet P p H x U).ι ≫ FixedNodeHom.toC P p H x) :=
    ⟨qmap, by rw [← Category.assoc, hq]; exact tF.property⟩
  refine ⟨q, ?_⟩
  have he : fixedPoint P p H x U q = tF := Subtype.ext hq
  rw [he, curveAt_forget, FixedNodeHom.forget_lift]
  exact hf

end FixedNeighborhood

/-- A reduced target's regular functions are detected by complex
points of any locally finite type source whose actual image is dense.
The source itself need not be reduced. -/
theorem function_zero_of_dense_complex_images {Y Z : Scheme}
    (sY : Y ⟶ ComplexBase) [LocallyOfFiniteType sY]
    [AlgebraicGeometry.IsReduced Z] (f : Y ⟶ Z) (hf : DenseRange f.base)
    (a : RingSections Z ⊤)
    (ha : ∀ q : PointsOver ComplexBase (𝟙 ComplexBase) Y sY,
      (q.val ≫ f).appTop a = 0) : a = 0 := by
  letI : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  apply AlgebraicGeometry.eq_zero_of_basicOpen_eq_bot a
  apply TopologicalSpace.Opens.ext
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨w, hw, y, rfl⟩ := hf.inter_open_nonempty
    (Z.basicOpen a : Set Z) (Z.basicOpen a).isOpen ⟨z, hz⟩
  have hd : Dense (closedPoints Y) := by
    rw [dense_iff_closure_eq, closure_closedPoints]
  obtain ⟨y₀, hy₀, hclosed⟩ := hd.inter_open_nonempty
    (f ⁻¹ᵁ Z.basicOpen a : Set Y) (f ⁻¹ᵁ Z.basicOpen a).isOpen ⟨y, hw⟩
  let q : PointsOver ComplexBase (𝟙 ComplexBase) Y sY :=
    ⟨pointOfClosedPoint sY y₀ hclosed, pointOfClosedPoint_comp sY y₀ hclosed⟩
  have hp : (q.val ≫ f) ⁻¹ᵁ Z.basicOpen a = ⊥ := by
    rw [Scheme.preimage_basicOpen_top, ha q]
    simp
  have hmem : IsLocalRing.closedPoint ℂ ∈ (q.val ≫ f) ⁻¹ᵁ Z.basicOpen a := by
    change f (q.val (IsLocalRing.closedPoint ℂ)) ∈ Z.basicOpen a
    change f y₀ ∈ Z.basicOpen a at hy₀
    simpa only [q, pointOfClosedPoint_apply] using hy₀
  rw [hp] at hmem
  exact hmem

namespace VelocityPolynomial

variable {A : Type} [CommRing A] [Algebra ℂ A] (p : A →ₐ[ℂ] ℂ)

instance pointDifferentials_finite [FiniteDimensional ℂ (Infinitesimal.Tangent A p)] :
    FiniteDimensional ℂ (AffineVelocity.PointDifferentials p) := by
  letI : FiniteDimensional ℂ (Module.Dual ℂ (AffineVelocity.PointDifferentials p)) :=
    FiniteDimensional.of_injective (LinearVelocityTarget.functionalEquiv p).symm.toLinearMap
      (LinearVelocityTarget.functionalEquiv p).symm.injective
  exact (Module.finite_dual_iff ℂ).1 inferInstance

variable [FiniteDimensional ℂ (Infinitesimal.Tangent A p)]

/-- The regular linear coordinate attached to a genuine linear
functional on point derivations. Reflexivity is used only for this
finite-dimensional vector space, with its canonical differential pairing. -/
def linear (ell : Infinitesimal.Tangent A p →ₗ[ℂ] ℂ) :
    AffineVelocity.CoordinateRing p :=
  SymmetricAlgebra.ι ℂ (AffineVelocity.PointDifferentials p)
    ((Module.evalEquiv ℂ (AffineVelocity.PointDifferentials p)).symm
      (ell.comp (LinearVelocityTarget.functionalEquiv p).symm.toLinearMap))

def evaluation (v : Infinitesimal.Tangent A p) :
    AffineVelocity.CoordinateRing p →ₐ[ℂ] ℂ :=
  (AffineVelocity.tangentPointEquiv p).symm v

theorem evaluation_coordinate (v : Infinitesimal.Tangent A p) (a : A) :
    evaluation p v (AffineVelocity.coordinate p a) = v.val a := by
  exact AffineVelocity.coordinateLift_coordinate p _ _ a

theorem evaluation_linear (v : Infinitesimal.Tangent A p)
    (ell : Infinitesimal.Tangent A p →ₗ[ℂ] ℂ) :
    evaluation p v (linear p ell) = ell v := by
  change SymmetricAlgebra.lift (LinearVelocityTarget.functional p v)
      (SymmetricAlgebra.ι ℂ (AffineVelocity.PointDifferentials p)
        ((Module.evalEquiv ℂ (AffineVelocity.PointDifferentials p)).symm
          (ell.comp (LinearVelocityTarget.functionalEquiv p).symm.toLinearMap))) = ell v
  rw [SymmetricAlgebra.lift_ι_apply, Module.apply_evalEquiv_symm_apply]
  change ell ((LinearVelocityTarget.functionalEquiv p).symm
    (LinearVelocityTarget.functionalEquiv p v)) = ell v
  rw [LinearEquiv.symm_apply_apply]

/-- The quadratic difference between the mixed coefficient tensor
and the prescribed square of a point covector. -/
def defect {N : ℕ} (a b : Fin N → A)
    (ell : Infinitesimal.Tangent A p →ₗ[ℂ] ℂ) :
    AffineVelocity.CoordinateRing p :=
  (∑ i, AffineVelocity.coordinate p (a i) * AffineVelocity.coordinate p (b i)) +
    2 * (linear p ell) ^ 2

theorem evaluation_defect {N : ℕ} (a b : Fin N → A)
    (ell : Infinitesimal.Tangent A p →ₗ[ℂ] ℂ) (v : Infinitesimal.Tangent A p) :
    evaluation p v (defect p a b ell) =
      (∑ i, v.val (a i) * v.val (b i)) + 2 * (ell v) ^ 2 := by
  simp only [defect, map_add, map_sum, map_mul, map_pow, map_ofNat,
    evaluation_coordinate, evaluation_linear]

/-- A dominant first-jet family detects the actual quadratic
polynomial, using complex points of its actual parameter scheme. -/
theorem eq_zero_of_dense {Y : Scheme} (sY : Y ⟶ ComplexBase)
    [LocallyOfFiniteType sY] (f : Y ⟶ AffineVelocity.tangentScheme p)
    (hf : DenseRange f.base) (q : AffineVelocity.CoordinateRing p)
    (hq : ∀ y : PointsOver ComplexBase (𝟙 ComplexBase) Y sY,
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
        ((y.val ≫ f).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (AffineVelocity.CoordinateRing p))).inv q)) = 0) :
    q = 0 := by
  have hz : (Scheme.ΓSpecIso (CommRingCat.of (AffineVelocity.CoordinateRing p))).inv q = 0 := by
    apply function_zero_of_dense_complex_images sY f hf
    intro y
    apply (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).injective
    rw [map_zero]
    exact hq y
  have h := congrArg (Scheme.ΓSpecIso (CommRingCat.of (AffineVelocity.CoordinateRing p))).hom hz
  simpa only [Iso.inv_hom_id_apply, map_zero] using h

end VelocityPolynomial

instance targetChart_tangent_finite {d : ℕ} {X : SmoothProperComplexVariety d}
    {x : ComplexPoint X} (C : GlobalVelocity.TargetChart X x) :
    FiniteDimensional ℂ (Infinitesimal.Tangent C.Ring C.evaluation) := by
  letI : FiniteDimensional ℂ (TangentFiber X x) :=
    fiber_finite (intrinsicTangentBundle X) x.map
  exact FiniteDimensional.of_injective (IntrinsicTangent.chartEquivalence C).symm.toLinearMap
    (IntrinsicTangent.chartEquivalence C).symm.injective

/-- The two point-derivation models are compared through their actual
intrinsic tangent fiber, retaining every local differential evaluation. -/
def frameChartTangentEquiv {d : ℕ} {X : SmoothProperComplexVariety d}
    {L : LineBundle X.scheme} {x : ComplexPoint X}
    (F : PointFrame X L x) (C : GlobalVelocity.TargetChart X x) :
    Infinitesimal.Tangent C.Ring C.evaluation ≃ₗ[ℂ] F.Tangent :=
  (IntrinsicTangent.chartEquivalence C).symm.trans F.fiberEquiv

theorem frameChartTangentEquiv_function {d : ℕ} {X : SmoothProperComplexVariety d}
    {L : LineBundle X.scheme} {x : ComplexPoint X}
    (F : PointFrame X L x) (C : GlobalVelocity.TargetChart X x)
    (hC : (⊤ : (Spec (CommRingCat.of C.Ring)).Opens) ≤ C.inclusion ⁻¹ᵁ F.frame.openSet)
    (v : Infinitesimal.Tangent C.Ring C.evaluation) (a : F.ChartRing) :
    (frameChartTangentEquiv F C v).val a = v.val (C.localCoordinate F.frame.openSet hC a) := by
  have h := IntrinsicTangent.chartEvaluation_localCoordinate C F.frame.openSet hC
    F.pointSupport a ((IntrinsicTangent.chartEquivalence C).symm v)
  have he : IntrinsicTangent.chartEvaluation C
      ((IntrinsicTangent.chartEquivalence C).symm v) = v :=
    (IntrinsicTangent.chartEquivalence C).apply_symm_apply v
  rw [he] at h
  exact h.symm

/-- The original differential at a point differentiates the actual
pullback of every frame function, on any smaller source affine frame. -/
theorem pointDifferential_frame_function {e d : ℕ}
    (Y : SmoothProperComplexVariety e) (X : SmoothProperComplexVariety d)
    (f : Y.scheme ⟶ X.scheme) (hf : f ≫ X.structureMap = Y.structureMap)
    (y : ComplexPoint Y) (x : ComplexPoint X) (hx : y.map ≫ f = x.map)
    {M : LineBundle Y.scheme} {L : LineBundle X.scheme}
    (S : PointFrame Y M y) (F : PointFrame X L x)
    (hV : S.frame.openSet ≤ f ⁻¹ᵁ F.frame.openSet)
    (u : SectionsOn (tangentSheaf Y.structureMap) S.frame.openSet)
    (a : F.ChartRing) :
    (F.fiberEquiv (SourceTangent.pointDifferential Y X f hf y x hx
      (PositiveFrame.localFiberValue y.map (tangentSheaf Y.structureMap)
        S.frame.openSet S.pointSupport u))).val a =
      S.evaluation (tangentActs Y.structureMap S.frame.openSet u
        (f.appLE F.frame.openSet S.frame.openSet hV a)) := by
  have hp : ⊤ ≤ y.map ⁻¹ᵁ (f ⁻¹ᵁ F.frame.openSet) := by
    change ⊤ ≤ (y.map ≫ f) ⁻¹ᵁ F.frame.openSet
    rw [hx]
    exact F.pointSupport
  change PositiveFrame.localScalarPairing x.map
      (dualEvaluation (cotangentSheaf X.structureMap)) F.frame.openSet F.pointSupport
      ((cotangentPresentation X.structureMap).differential.apply F.frame.openSet a)
      (SourceTangent.pointDifferential Y X f hf y x hx
        (PositiveFrame.localFiberValue y.map (tangentSheaf Y.structureMap)
          S.frame.openSet S.pointSupport u)) = _
  rw [SourceTangent.pointDifferential_local_pairing Y X f hf y x hx
    F.frame.openSet hp F.pointSupport]
  rw [← SourceTangent.localScalarPairing_restrict y.map
    (dualEvaluation (cotangentSheaf Y.structureMap)) hV S.pointSupport hp]
  rw [(cotangentPresentation Y.structureMap).differential.naturality,
    PositiveFrame.localScalarPairing_value]
  exact (S.evaluation_eq_localRingValue _).symm

/-- The point contact covector is the actual contact quotient in the
specified line-fiber frame. Surjectivity of evaluation is used only to
verify that these two already defined linear functionals agree. -/
theorem theta_fiber_coefficient {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
    (C : IntrinsicContactStructure X) {x : ComplexPoint X}
    (F : PointFrame X C.sequence.line x) (A : ContactAtPoint C F)
    (v : TangentFiber X x) :
    A.theta (F.fiberEquiv v) =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
        (F.lineFiberCoefficient (fiberMap C.sequence.form x.map v)) := by
  obtain ⟨u, hu⟩ := F.evaluateVector_surjective (F.fiberEquiv v)
  have hv : PositiveFrame.localFiberValue x.map (tangentSheaf X.structureMap)
      F.frame.openSet F.pointSupport u = v :=
    F.fiberEquiv.injective ((F.fiberEquiv_local u).trans hu)
  rw [← hv, F.fiberEquiv_local, A.theta_normalized,
    ← PositiveFrame.localFiberValue_map]
  have hc := F.lineFiberCoefficient_local
    (F.frame.coefficient (C.sequence.form.app F.frame.openSet u))
  rw [F.frame.coefficient.symm_apply_apply] at hc
  rw [hc]
  exact F.evaluation_eq_localRingValue (localContactValue C F.frame u)

/-- The mixed source identity written in the actual pullbacks of the
target frame functions. This is precisely where the line-frame pullback
normalization is used; no coefficient is replaced by an arbitrary model. -/
theorem source_curve_mixed_coefficients (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {n : ℕ}
    {X : SmoothProperComplexVariety (2*n+1)} (C : IntrinsicContactStructure X)
    (f : RationalCurve P X) {B : ExternalSquareSections X C.sequence.line}
    (h : CurveKernelIdentity P C f B) (E : ExternalExpansion X C.sequence.line B)
    {x : ComplexPoint X} (F : PointFrame X C.sequence.line x)
    (S : PointFrame (projectiveLineVariety P) (identityCurveContact P).sequence.line
      ⟨p.map, p.overC⟩)
    (hV : S.frame.openSet ≤ f.map ⁻¹ᵁ F.frame.openSet)
    (u : SectionsOn (tangentSheaf P.structureMap) S.frame.openSet) :
    (∑ i, tangentActs P.structureMap S.frame.openSet u
        (f.map.appLE F.frame.openSet S.frame.openSet hV (F.coefficient (E.left i))) *
      tangentActs P.structureMap S.frame.openSet u
        (f.map.appLE F.frame.openSet S.frame.openSet hV (F.coefficient (E.right i)))) =
      -2 * (PointFrame.LocalFrameJetProof.coefficientOn F.frame f.map S.frame.openSet hV
        ((curveContactVelocity P C f).app S.frame.openSet u)) ^ 2 := by
  let m := PointFrame.LocalFrameJetProof.coefficientOn F.frame f.map S.frame.openSet hV
  have hc (a : AlgebraicSection C.sequence.line.sheaf) :
      (SourceMixedSymbol.frameOn (M := pullbackBundle f.map C.sequence.line) S.frame m).localCoefficient
        (pullSection f.map a) =
      f.map.appLE F.frame.openSet S.frame.openSet hV (F.coefficient a) := by
    change m (Scheme.Modules.Hom.app (pullSection f.map a)
      S.frame.openSet (1 : RingSections ProjectiveLine _)) = _
    rw [ScalarSections.section_app_one]
    exact PointFrame.LocalFrameJetProof.coefficientOn_global F.frame f.map S.frame.openSet hV a
  have hs := SourceMixedSymbol.source_curve_mixed P C f B h E S.frame m u
  simp_rw [hc] at hs
  exact hs

/-- Every actual curve identity imposes the quadratic identity on the
actual differential of every source dual point. The proof uses a local
source vector representing that point, then the normalized fiber maps. -/
theorem curve_point_quadratic (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {n : ℕ}
    {X : SmoothProperComplexVariety (2*n+1)} (C : IntrinsicContactStructure X)
    (f : RationalCurve P X) {B : ExternalSquareSections X C.sequence.line}
    (h : CurveKernelIdentity P C f B) (E : ExternalExpansion X C.sequence.line B)
    {x : ComplexPoint X} (hx : p.map ≫ f.map = x.map)
    (F : PointFrame X C.sequence.line x) (A : ContactAtPoint C F)
    (tau : HomFirstJet.SourceLift P p) :
    let w := SourceTangent.pointDifferential (projectiveLineVariety P) X
      f.map f.overC ⟨p.map, p.overC⟩ x hx
      (SourceTangent.pointVector (projectiveLineVariety P) ⟨p.map, p.overC⟩ tau)
    (∑ i, (F.fiberEquiv w).val (F.coefficient (E.left i)) *
      (F.fiberEquiv w).val (F.coefficient (E.right i))) +
      2 * (A.theta (F.fiberEquiv w)) ^ 2 = 0 := by
  let y : ComplexPoint (projectiveLineVariety P) := ⟨p.map, p.overC⟩
  let v := SourceTangent.pointVector (projectiveLineVariety P) y tau
  let w := SourceTangent.pointDifferential (projectiveLineVariety P) X
    f.map f.overC y x hx v
  change (∑ i, (F.fiberEquiv w).val (F.coefficient (E.left i)) *
    (F.fiberEquiv w).val (F.coefficient (E.right i))) +
      2 * (A.theta (F.fiberEquiv w)) ^ 2 = 0
  have hpU : ⊤ ≤ p.map ⁻¹ᵁ (f.map ⁻¹ᵁ F.frame.openSet) := by
    change ⊤ ≤ (p.map ≫ f.map) ⁻¹ᵁ F.frame.openSet
    rw [hx]
    exact F.pointSupport
  obtain ⟨S, hV⟩ := pointFrame_inside (projectiveLineVariety P)
    (identityCurveContact P).sequence.line y (f.map ⁻¹ᵁ F.frame.openSet) hpU
  obtain ⟨u, hu⟩ := S.evaluateVector_surjective (S.fiberEquiv v)
  have hu' : PositiveFrame.localFiberValue p.map (tangentSheaf P.structureMap)
      S.frame.openSet S.pointSupport u = v :=
    S.fiberEquiv.injective ((S.fiberEquiv_local u).trans hu)
  let m := PointFrame.LocalFrameJetProof.coefficientOn F.frame f.map S.frame.openSet hV
  have hD (a : F.ChartRing) : (F.fiberEquiv w).val a =
      S.evaluation (tangentActs P.structureMap S.frame.openSet u
        (f.map.appLE F.frame.openSet S.frame.openSet hV a)) := by
    dsimp only [w]
    rw [← hu']
    exact pointDifferential_frame_function (projectiveLineVariety P) X
      f.map f.overC y x hx S F hV u a
  have hform : fiberMap C.sequence.form x.map w =
      fiberComposition f.map p.map x.map hx C.sequence.line.sheaf
        (PositiveFrame.localFiberValue p.map (pullbackModule f.map C.sequence.line.sheaf)
          S.frame.openSet S.pointSupport ((curveContactVelocity P C f).app S.frame.openSet u)) := by
    rw [PositiveFrame.localFiberValue_map, hu']
    change fiberMap C.sequence.form x.map
      (fiberComposition f.map p.map x.map hx (tangentSheaf X.structureMap)
        (fiberMap (differentialOver (projectiveLineVariety P) X f.map f.overC) p.map v)) =
      fiberComposition f.map p.map x.map hx C.sequence.line.sheaf
        (fiberMap (differentialOver (projectiveLineVariety P) X f.map f.overC ≫
          (Scheme.Modules.pullback f.map).map C.sequence.form) p.map v)
    rw [ContactPositive.fiberMap_comp]
    exact (ContactPositive.fiberComposition_naturality f.map p.map x.map hx
      C.sequence.form (fiberMap
        (differentialOver (projectiveLineVariety P) X f.map f.overC) p.map v)).symm
  have htheta : A.theta (F.fiberEquiv w) =
      S.evaluation (m ((curveContactVelocity P C f).app S.frame.openSet u)) := by
    rw [theta_fiber_coefficient C F A, hform,
      F.lineFiberCoefficient_composition f.map p.map hx S.frame.openSet hV S.pointSupport]
    exact (S.evaluation_eq_localRingValue _).symm
  have hm := congrArg S.evaluation
    (source_curve_mixed_coefficients P p C f h E F S hV u)
  simp only [map_sum, map_mul, map_neg, map_ofNat, map_pow] at hm
  simp_rw [hD]
  rw [htheta]
  change (∑ i, S.evaluation (tangentActs P.structureMap S.frame.openSet u
      (f.map.appLE F.frame.openSet S.frame.openSet hV (F.coefficient (E.left i)))) *
    S.evaluation (tangentActs P.structureMap S.frame.openSet u
      (f.map.appLE F.frame.openSet S.frame.openSet hV (F.coefficient (E.right i)))) ) +
    2 * S.evaluation (m ((curveContactVelocity P C f).app S.frame.openSet u)) ^ 2 = 0
  linear_combination hm

def frameDefect {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
    {C : IntrinsicContactStructure X} {B : ExternalSquareSections X C.sequence.line}
    (E : ExternalExpansion X C.sequence.line B) {x : ComplexPoint X}
    (F : PointFrame X C.sequence.line x) (A : ContactAtPoint C F)
    (G : GlobalVelocity.TargetChart X x)
    (hG : (⊤ : (Spec (CommRingCat.of G.Ring)).Opens) ≤ G.inclusion ⁻¹ᵁ F.frame.openSet) :
    AffineVelocity.CoordinateRing G.evaluation :=
  VelocityPolynomial.defect G.evaluation
    (fun i => G.localCoordinate F.frame.openSet hG (F.coefficient (E.left i)))
    (fun i => G.localCoordinate F.frame.openSet hG (F.coefficient (E.right i)))
    (A.theta.comp (frameChartTangentEquiv F G).toLinearMap)

theorem frameDefect_evaluation {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
    {C : IntrinsicContactStructure X} {B : ExternalSquareSections X C.sequence.line}
    (E : ExternalExpansion X C.sequence.line B) {x : ComplexPoint X}
    (F : PointFrame X C.sequence.line x) (A : ContactAtPoint C F)
    (G : GlobalVelocity.TargetChart X x)
    (hG : (⊤ : (Spec (CommRingCat.of G.Ring)).Opens) ≤ G.inclusion ⁻¹ᵁ F.frame.openSet)
    (v : Infinitesimal.Tangent G.Ring G.evaluation) :
    VelocityPolynomial.evaluation G.evaluation v (frameDefect E F A G hG) =
      (∑ i, (frameChartTangentEquiv F G v).val (F.coefficient (E.left i)) *
        (frameChartTangentEquiv F G v).val (F.coefficient (E.right i))) +
      2 * (A.theta (frameChartTangentEquiv F G v)) ^ 2 := by
  rw [frameDefect, VelocityPolynomial.evaluation_defect]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    frameChartTangentEquiv_function F G hG]

theorem homValue_polynomial (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {d : ℕ} {X : SmoothProperComplexVariety d} (H : HomSpacePresentation P X)
    (x : ComplexPoint X) (tau : HomFirstJet.SourceLift P p)
    (G : GlobalVelocity.TargetChart X x)
    (t : PointsOver ComplexBase (𝟙 ComplexBase)
      (FixedNodeHom.parameter P p H x) (FixedNodeHom.toC P p H x))
    (q : AffineVelocity.CoordinateRing G.evaluation) :
    VelocityPolynomial.evaluation G.evaluation (ActualHomVelocity.value P p H x tau G t) q =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
        ((t.val ≫ GlobalVelocity.homVelocity P p H x tau G).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (AffineVelocity.CoordinateRing G.evaluation))).inv q)) := by
  unfold VelocityPolynomial.evaluation ActualHomVelocity.value HomVelocityValue.tangentValue
  rw [Equiv.symm_apply_apply]
  rfl

/-- At every point lying on one of the actual very-free family members,
the quadratic defect vanishes on the entire intrinsic tangent space.
The only geometric input here is the approved generic first-jet
restriction theorem for the actual fixed-node Hom open. -/
theorem frameDefect_zero_on_curve (P : ProjectiveLineOverC)
    (p₀ : ProjectiveLinePoint P) {n : ℕ} (X : ContactFanoManifold n)
    (g : VeryFreeContactConic P p₀ X) (D : FamilyKernel P p₀ X g)
    (E : ExternalExpansion X.variety X.contact.sequence.line D.kernel)
    (t : PointsOver ComplexBase (𝟙 ComplexBase) D.family.neighborhood.toScheme
      (D.family.neighborhood.ι ≫ D.family.homSpace.toC))
    (p : ProjectiveLinePoint P) (x : ComplexPoint X.variety)
    (hx : p.map ≫ (D.family.curveAt t).map = x.map)
    (F : PointFrame X.variety X.contact.sequence.line x) (A : ContactAtPoint X.contact F)
    (G : GlobalVelocity.TargetChart X.variety x)
    (hG : (⊤ : (Spec (CommRingCat.of G.Ring)).Opens) ≤ G.inclusion ⁻¹ᵁ F.frame.openSet) :
    frameDefect E F A G hG = 0 := by
  let H := D.family.homSpace
  let U := D.family.neighborhood
  let V := FixedNeighborhood.openSet P p H x U
  let sV := V.ι ≫ FixedNodeHom.toC P p H x
  letI : LocallyOfFiniteType sV :=
    FixedNeighborhood.locallyOfFiniteType P p H x U D.family.smooth
  obtain ⟨tau, htau⟩ := sourceLift_nonconstant P p
  obtain ⟨center, hcenter⟩ := FixedNeighborhood.point_exists P p H x U t
    (D.family.curveAt t) (D.family.curveAt_spec t) hx
  have hdense : DenseRange (V.ι ≫ GlobalVelocity.homVelocity P p H x tau G).base :=
    LeBrunSalamon.StandardInputs.homOpen_sourceFirstJet_dominant P p X.variety H x
      tau htau G V center (D.family.curveAt t) hcenter (D.family.veryFree t)
  apply VelocityPolynomial.eq_zero_of_dense G.evaluation sV
    (V.ι ≫ GlobalVelocity.homVelocity P p H x tau G) hdense
  intro q
  let qF := FixedNeighborhood.fixedPoint P p H x U q
  let tq := FixedNeighborhood.familyPoint P p H x U q
  let fq := D.family.curveAt tq
  have hfq : fq.map = HomDeformation.curveAt P H p x qF :=
    (D.family.curveAt_spec tq).trans
      (FixedNeighborhood.curveAt_fixedPoint P p H x U q).symm
  have hxq : p.map ≫ fq.map = x.map := by
    rw [hfq, HomDeformation.curveAt_marking]
  let w := SourceTangent.pointDifferential (projectiveLineVariety P) X.variety
    fq.map fq.overC ⟨p.map, p.overC⟩ x hxq
    (SourceTangent.pointVector (projectiveLineVariety P) ⟨p.map, p.overC⟩ tau)
  have hv : ActualHomVelocity.value P p H x tau G qF =
      IntrinsicTangent.chartEquivalence G w := by
    simpa only [w, hfq] using
      ActualHomVelocity.value_eq_pointDifferential P p H x tau G qF
  have hz : VelocityPolynomial.evaluation G.evaluation
      (ActualHomVelocity.value P p H x tau G qF) (frameDefect E F A G hG) = 0 := by
    rw [frameDefect_evaluation, hv]
    simpa only [frameChartTangentEquiv, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply] using
      curve_point_quadratic P p X.contact fq (D.fullIdentity tq) E hxq F A tau
  rw [homValue_polynomial] at hz
  simpa only [qF, FixedNeighborhood.fixedPoint, Category.assoc] using hz

/-- The actual family detects regular functions on every open of the
target. The tests are actual source points whose images lie in that
open, with their specified lifts; all density is supplied by the proved
universal evaluation comparison. -/
theorem function_zero_on_full_family (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {n : ℕ} (X : ContactFanoManifold n)
    (g : VeryFreeContactConic P p X) (H : FullConicNeighborhood P p X g)
    (U : X.variety.scheme.Opens) (a : RingSections X.variety.scheme U)
    (h : ∀ (t : PointsOver ComplexBase (𝟙 ComplexBase) H.neighborhood.toScheme
      (H.neighborhood.ι ≫ H.homSpace.toC)) (r : ProjectiveLinePoint P)
      (q : ComplexBase ⟶ U.toScheme),
      q ≫ U.ι = r.map ≫ (H.curveAt t).map →
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (q.appTop (U.topIso.inv a)) = 0) :
    a = 0 := by
  let Z := HomTwoPointEvaluation.Source P H.homSpace H.neighborhood
  let s : Z ⟶ ComplexBase := HomTwoPointEvaluation.structureMap P H.homSpace H.neighborhood
  let e := HomTwoPointEvaluation.evaluation P H.homSpace H.neighborhood
  let ev : Z ⟶ X.variety.scheme := e ≫ firstProjection X.variety.structureMap
  letI : Smooth s := HomTwoPointEvaluation.source_smooth P H.homSpace H.neighborhood H.smooth
  have he : DenseRange e.base :=
    LeBrunSalamon.StandardInputs.homOpen_twoPointEvaluation_dominant P X.variety
      H.homSpace H.neighborhood H.smooth H.marked (H.curveAt H.marked)
      (H.curveAt_spec H.marked) (H.veryFree H.marked)
  have hp : Function.Surjective (firstProjection X.variety.structureMap) := by
    intro z
    exact ⟨diagonal X.variety.structureMap z,
      congrArg (fun k : X.variety.scheme ⟶ X.variety.scheme => k z)
        (pullback.diagonal_fst X.variety.structureMap)⟩
  letI : IsDominant ev :=
    ⟨hp.denseRange.comp he (firstProjection X.variety.structureMap).continuous⟩
  let W := ev ⁻¹ᵁ U
  let r := ev.resLE U W le_rfl
  letI : LocallyOfFiniteType (W.ι ≫ s) := inferInstance
  letI : Smooth (U.ι ≫ X.variety.structureMap) := inferInstance
  letI : AlgebraicGeometry.IsReduced U.toScheme :=
    LeBrunSalamon.SchemeStandardInputs.smooth_complex_reduced (U.ι ≫ X.variety.structureMap)
  have hr : DenseRange r.base := by
    have hd : IsDominant (ev ∣_ U) := IsZariskiLocalAtTarget.restrict
      (show IsDominant ev from inferInstance) U
    letI := hd
    simpa only [r, W, Scheme.Hom.resLE_eq_morphismRestrict] using
      (ev ∣_ U).denseRange
  have hz : U.topIso.inv a = 0 := by
    apply function_zero_of_dense_complex_images (W.ι ≫ s) r hr
    intro q
    let qZ : PointsOver ComplexBase (𝟙 ComplexBase) Z s :=
      ⟨q.val ≫ W.ι, by simpa only [Category.assoc] using q.property⟩
    let t := HomTwoPointEvaluation.pointParameter P H.homSpace H.neighborhood qZ
    let z : ComplexBase ⟶ SelfProduct P.structureMap :=
      qZ.val ≫ pullback.fst (HomTwoPointEvaluation.squareStructure P)
        (H.neighborhood.ι ≫ H.homSpace.toC)
    have hzb : z ≫ HomTwoPointEvaluation.squareStructure P = 𝟙 ComplexBase := by
      calc
        _ = qZ.val ≫ s := by
          rw [Category.assoc, pullback.condition]
        _ = _ := qZ.property
    let p' : ProjectiveLinePoint P :=
      ⟨z ≫ firstProjection P.structureMap, by
        simpa only [HomTwoPointEvaluation.squareStructure, Category.assoc] using hzb⟩
    have hfiber := HomTwoPointEvaluation.fiberInclusion_evaluation P H.homSpace
      H.neighborhood t (H.curveAt t) (H.curveAt_spec t)
    have hfactor : z ≫ HomTwoPointEvaluation.fiberInclusion P H.homSpace H.neighborhood t =
        qZ.val := HomTwoPointEvaluation.point_factorization P H.homSpace H.neighborhood qZ
    have hc : z ≫ curveSquareMap P (H.curveAt t) = qZ.val ≫ e := by
      rw [← hfiber, ← Category.assoc, hfactor]
    have hpoint : p'.map ≫ (H.curveAt t).map = qZ.val ≫ ev := by
      change (z ≫ firstProjection P.structureMap) ≫ (H.curveAt t).map =
        qZ.val ≫ (e ≫ firstProjection X.variety.structureMap)
      rw [Category.assoc, ← curveSquareMap_first, ← Category.assoc, hc, Category.assoc]
    have hq : (q.val ≫ r) ≫ U.ι = p'.map ≫ (H.curveAt t).map := by
      rw [hpoint]
      change (q.val ≫ ev.resLE U W le_rfl) ≫ U.ι = (q.val ≫ W.ι) ≫ ev
      rw [Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).injective
    rw [map_zero]
    exact h t p' (q.val ≫ r) hq
  apply (ConcreteCategory.bijective_of_isIso U.topIso.inv).injective
  rw [map_zero]
  exact hz

/-- Vanishing of the actual quadratic velocity polynomial gives the
undivided Hessian on a repeated intrinsic vector. The first symbol is
used in the already proved identity mixedSecond = -secondSlotSecond. -/
theorem pointHessian_self_of_defect_zero {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
    {C : IntrinsicContactStructure X} {B : ExternalSquareSections X C.sequence.line}
    (E : ExternalExpansion X C.sequence.line B)
    (h1 : VanishesQuadraticallyAlongDiagonal X.structureMap
      (externalSquareLine X.structureMap C.sequence.line).sheaf B)
    {x : ComplexPoint X} (F : PointFrame X C.sequence.line x) (A : ContactAtPoint C F)
    (G : GlobalVelocity.TargetChart X x)
    (hG : (⊤ : (Spec (CommRingCat.of G.Ring)).Opens) ≤ G.inclusion ⁻¹ᵁ F.frame.openSet)
    (hq : frameDefect E F A G hG = 0)
    (u : SectionsOn (tangentSheaf X.structureMap) F.frame.openSet) :
    F.evaluation (E.secondSlotSecond F.frame u u) =
      2 * (F.evaluation (localContactValue C F.frame u)) ^ 2 := by
  let v := (frameChartTangentEquiv F G).symm (F.evaluateVector u)
  have hz := congrArg (VelocityPolynomial.evaluation G.evaluation v) hq
  rw [frameDefect_evaluation, map_zero] at hz
  have hv : frameChartTangentEquiv F G v = F.evaluateVector u :=
    (frameChartTangentEquiv F G).apply_symm_apply _
  rw [hv, A.theta_normalized] at hz
  have hmix : (∑ i, (F.evaluateVector u).val (F.coefficient (E.left i)) *
      (F.evaluateVector u).val (F.coefficient (E.right i))) =
      F.evaluation (E.mixedSecond F.frame u u) := by
    simp only [ExternalExpansion.mixedSecond, map_sum, map_mul]
    rfl
  rw [hmix, E.mixedSecond_eq_neg_of_orderTwo h1 F.frame u u, map_neg] at hz
  linear_combination -hz

/-- Polarization supplies the mixed undivided Hessian, with symmetry
justified by order-two vanishing before the calculation. -/
theorem pointHessian_of_defect_zero {n : ℕ} {X : SmoothProperComplexVariety (2*n+1)}
    {C : IntrinsicContactStructure X} {B : ExternalSquareSections X C.sequence.line}
    (E : ExternalExpansion X C.sequence.line B)
    (h1 : VanishesQuadraticallyAlongDiagonal X.structureMap
      (externalSquareLine X.structureMap C.sequence.line).sheaf B)
    {x : ComplexPoint X} (F : PointFrame X C.sequence.line x) (A : ContactAtPoint C F)
    (G : GlobalVelocity.TargetChart X x)
    (hG : (⊤ : (Spec (CommRingCat.of G.Ring)).Opens) ≤ G.inclusion ⁻¹ᵁ F.frame.openSet)
    (hq : frameDefect E F A G hG = 0)
    (u v : SectionsOn (tangentSheaf X.structureMap) F.frame.openSet) :
    F.evaluation (E.secondSlotSecond F.frame u v) =
      2 * F.evaluation (localContactValue C F.frame u) *
        F.evaluation (localContactValue C F.frame v) := by
  have hu := pointHessian_self_of_defect_zero E h1 F A G hG hq u
  have hv := pointHessian_self_of_defect_zero E h1 F A G hG hq v
  have huv := pointHessian_self_of_defect_zero E h1 F A G hG hq (u + v)
  have hs : E.secondSlotSecond F.frame (u + v) (u + v) =
      E.secondSlotSecond F.frame u u + E.secondSlotSecond F.frame u v +
        E.secondSlotSecond F.frame v u + E.secondSlotSecond F.frame v v := by
    simp only [ExternalExpansion.secondSlotSecond, tangentActs_add_field,
      tangentActs_add_function, mul_add, Finset.sum_add_distrib]
    abel
  have ht : localContactValue C F.frame (u + v) =
      localContactValue C F.frame u + localContactValue C F.frame v := by
    simp only [localContactValue, map_add]
  rw [hs, ht, E.secondSlotSecond_symmetric_of_orderTwo h1 F.frame v u,
    map_add, map_add, map_add, map_add] at huv
  linear_combination (1 / 2 : ℂ) * huv - (1 / 2 : ℂ) * hu - (1 / 2 : ℂ) * hv

end ConicJetProof

end LeBrunSalamon.Refinement

end
