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

end
