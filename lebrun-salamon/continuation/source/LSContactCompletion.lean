import LSContactHorizontal
import LSPositiveHom
import LSPositiveIndependence

/-! The declarations formerly in this block were moved, with their
proofs unchanged, into RecompileExtensions before the three original
positive-node theorems. This module retains its public import path.
Source-order relocation: positive isotropy and rank block. No additional axiom is introduced. -/

/-!
## The manuscript's positive-part lemma and its suitable-pair consequences

SOURCE: `lines:positive` and the linear-algebra step of `lines:suitable-pair`.
The endpoint below joins the intrinsic positive subbundle and trivial quotient
to the newly proved contact-geometric horizontality, isotropy and rank bound.
It is a theorem about the original FreeLine, with no extra proof package.

The suitable-pair consequences explicitly use the new proved rank bound.
They do not use the three historical admitted positive-node assertions or
the admitted existence of a suitable pair. Existence is still a separate
manuscript obligation.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseEighteen LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction
open LeBrunSalamon.Construction.Lines

namespace LeBrunSalamon.Construction.Lines.ContactPositive

/-- The positive part from any other splitting is canonically
identified with the chosen actual positive bundle, over the original f*TX.
The point used to present the twists may also change. -/
theorem freeLine_positive_intrinsic {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (q : ProjectiveLinePoint P) {r : ℕ}
    (a : TangentSplittingProfile r)
    (e : (PositivePart.freeLineBundle f).sheaf ≅ splitSheaf P q a) :
    ∃ i : PositivePart.positiveSheaf P q a ≅ (PositivePart.freeLinePositiveBundle f).sheaf,
      i.hom ≫ PositivePart.freeLinePositiveInclusion f =
        PositivePart.positiveInclusion P q a e := by
  have ha : a.IsFree :=
    (P1SplitBundles.splitSheaf_globallyGenerated_iff P q a).mp
      ((DirectSumGeometry.globallyGenerated_iso_iff e).mp f.free)
  refine ⟨PositivePart.positivePartIso P q marking a (PositivePart.freeLineProfile f)
    e (PositivePart.freeLineSplitting f) ha (PositivePart.freeLineProfile_nonnegative f), ?_⟩
  exact PositivePart.positivePartIso_hom_inclusion P q marking a
    (PositivePart.freeLineProfile f) e (PositivePart.freeLineSplitting f)
    ha (PositivePart.freeLineProfile_nonnegative f)

/-- Every conclusion of `lines:positive`, for the actual free curve:
intrinsic positive inclusion, a trivial quotient in a short exact sequence,
horizontal containment, zero restricted intrinsic Levi map, and rank ≤ n.
The named dependency audit rejects the old admitted versions of the last
three assertions. -/
theorem freeLine_positive {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X) :
    (∀ (q : ProjectiveLinePoint P) (r : ℕ) (a : TangentSplittingProfile r),
      ∀ e : (PositivePart.freeLineBundle f).sheaf ≅ splitSheaf P q a,
        ∃ i : PositivePart.positiveSheaf P q a ≅ (PositivePart.freeLinePositiveBundle f).sheaf,
          i.hom ≫ PositivePart.freeLinePositiveInclusion f =
            PositivePart.positiveInclusion P q a e) ∧
    (ShortComplex.mk (PositivePart.freeLinePositiveInclusion f)
      (PositivePart.freeLineZeroProjection f) (PositivePart.freeLine_positive_zero f)).ShortExact ∧
    Nonempty ((PositivePart.freeLineZeroBundle f).sheaf ≅
      PositiveQuotient.trivialQuotientSheaf P marking
        (PositivePart.ZeroIndex (PositivePart.freeLineProfile f))) ∧
    PositivePart.freeLinePositiveInclusion f ≫ contactProjection f = 0 ∧
    tensorLift (ContactPositiveIsotropy.positiveLeviPair f) = 0 ∧
    Fintype.card (PositivePart.PositiveIndex (PositivePart.freeLineProfile f)) ≤ n := by
  refine ⟨?_, PositivePart.freeLine_shortExact f,
    ⟨PositivePart.freeLineZeroTrivialization f⟩, positiveHorizontal f,
    ContactPositiveIsotropy.positiveLevi_tensor_zero f, freeLine_positiveRank_le f⟩
  intro q r a e
  exact freeLine_positive_intrinsic f q a e

/-- The horizontal conclusion is invariant under changing the splitting,
because the comparison commutes with the actual inclusions into f*TX. -/
theorem freeLine_anyPositiveInclusion_horizontal {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (q : ProjectiveLinePoint P) {r : ℕ}
    (a : TangentSplittingProfile r)
    (e : (PositivePart.freeLineBundle f).sheaf ≅ splitSheaf P q a) :
    PositivePart.positiveInclusion P q a e ≫ contactProjection f = 0 := by
  obtain ⟨i, hi⟩ := freeLine_positive_intrinsic f q a e
  rw [← hi, Category.assoc, positiveHorizontal, comp_zero]

/-- The two actual positive node spaces of a suitable pair are disjoint.
Both rank bounds come from the proved contact argument in this namespace. -/
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
  have hfirst := ContactPositive.positiveNodeSpace_rank_le D.first D.node D.firstAtNode
  have hsecond := ContactPositive.positiveNodeSpace_rank_le D.second D.node D.secondAtNode
  apply disjoint_iff.mpr
  apply Submodule.finrank_eq_zero.mp
  omega

/-- Their dimensions are both n: a spanning pair in a 2n-dimensional
contact plane forces equality in the proved isotropic rank bounds. -/
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
  have hfirst := ContactPositive.positiveNodeSpace_rank_le D.first D.node D.firstAtNode
  have hsecond := ContactPositive.positiveNodeSpace_rank_le D.second D.node D.secondAtNode
  omega

/-- The same equalities hold for the actual positive subbundles, not
only for abstract node subspaces. -/
theorem suitablePair_positiveBundle_ranks {n : ℕ} {X : ContactFanoManifold n}
    (D : SuitablePair X) :
    Fintype.card (PositivePart.PositiveIndex (PositivePart.freeLineProfile D.first)) = n ∧
    Fintype.card (PositivePart.PositiveIndex (PositivePart.freeLineProfile D.second)) = n := by
  have h := suitablePair_positive_dimensions D
  rw [positiveNodeSpace_finrank_eq_positiveRank,
    positiveNodeSpace_finrank_eq_positiveRank] at h
  exact h

end LeBrunSalamon.Construction.Lines.ContactPositive

end

/-!
## The canonical curve differential lies in the actual positive part

The source tangent line is O(2), so its actual map to the constructed
degree-zero quotient vanishes. The actual positive retraction therefore
factors the canonical differential through the positive inclusion.
Taking the marked fiber proves membership of every original
nodeDifferential value in the original positiveNodeSpace.

This removes the extra positive-membership hypotheses required by the
earlier suitable-pair consumers. No new admitted input is introduced.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Lines.ContactPositive

/-- The canonical differential has zero component in the actual
degree-zero quotient. The original source tangent sheaf is retained. -/
theorem curveDifferential_zeroProjection {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) :
    curveDifferential f ≫ PositivePart.freeLineZeroProjection f = 0 := by
  let eT := (projectiveLine_tangent_twist P marking).some
  let eQ := PositivePart.freeLineZeroTrivialization f
  have hh : eT.inv ≫ curveDifferential f ≫
      PositivePart.freeLineZeroProjection f ≫ eQ.hom = 0 := by
    apply PositiveHom.hom_coproduct_eq_zero
      (fun _ : PositivePart.ZeroIndex (PositivePart.freeLineProfile f) =>
        (projectiveTwist P marking 0).sheaf)
    intro j
    exact PositiveHom.hom_twist_eq_zero_of_lt P marking marking 2 0 (by norm_num) _
  apply (cancel_mono eQ.hom).mp
  apply (cancel_epi eT.inv).mp
  simpa only [Category.assoc, comp_zero, zero_comp] using hh

/-- The original splitting gives an explicit actual positive retraction. -/
def positiveRetraction {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X) :
    (PositivePart.freeLineBundle f).sheaf ⟶ (PositivePart.freeLinePositiveBundle f).sheaf :=
  PositivePart.positiveRetraction P marking (PositivePart.freeLineProfile f)
    (PositivePart.freeLineSplitting f)

/-- The differential's actual positive factor, with no section choice
or arbitrary tangent-vector lift. -/
def positiveDifferential {n : ℕ} {X : ContactFanoManifold n} (f : FreeLine X) :
    tangentSheaf P.structureMap ⟶ (PositivePart.freeLinePositiveBundle f).sheaf :=
  curveDifferential f ≫ positiveRetraction f

@[reassoc]
theorem positiveDifferential_inclusion {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) :
    positiveDifferential f ≫ PositivePart.freeLinePositiveInclusion f = curveDifferential f := by
  exact PositiveHom.factor_through_split_inclusion
    (curveDifferential f) (PositivePart.freeLinePositiveInclusion f) (positiveRetraction f)
    (PositivePart.freeLineZeroProjection f)
    (PositivePart.zeroSection P marking (PositivePart.freeLineProfile f)
      (PositivePart.freeLineSplitting f))
    (PositivePart.split_total P marking (PositivePart.freeLineProfile f)
      (PositivePart.freeLineSplitting f) (PositivePart.freeLineProfile_nonnegative f))
    (curveDifferential_zeroProjection f)

/-- Every original node differential value lies in the original positive
node space. No positive-membership witness is an input to this theorem. -/
theorem nodeDifferential_mem_positiveNodeSpace {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map)
    (v : Fiber (tangentSheaf P.structureMap) marking.map) :
    nodeDifferential f x hx v ∈ positiveNodeSpace f x hx := by
  rw [PositiveNodeImage.freeLine_positiveNodeSpace_eq_fiberImage f x hx]
  refine ⟨fiberMap (positiveDifferential f) marking.map v, ?_⟩
  have hc := fiberMap_comp (positiveDifferential f)
    (PositivePart.freeLinePositiveInclusion f) marking.map v
  have hf := congrArg (fun k : tangentSheaf P.structureMap ⟶
      (PositivePart.freeLineBundle f).sheaf => fiberMap k marking.map v)
    (positiveDifferential_inclusion f)
  exact congrArg
    (fiberComposition f.curve.map marking.map x.map hx (tangentSheaf X.variety.structureMap))
    (hc.symm.trans hf)

/-- The canonical node tangent is horizontal by the newly proved actual
positive-node containment theorem. -/
theorem nodeDifferential_mem_contactPlane {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map)
    (v : Fiber (tangentSheaf P.structureMap) marking.map) :
    nodeDifferential f x hx v ∈ contactPlane X x :=
  positiveNodeSpace_horizontal f x hx (nodeDifferential_mem_positiveNodeSpace f x hx v)

/-- Scalar changes of the source tangent retain the original positive
node membership, including the zero scalar. -/
theorem smul_nodeDifferential_mem_positiveNodeSpace {n : ℕ} {X : ContactFanoManifold n}
    (f : FreeLine X) (x : ComplexPoint X.variety)
    (hx : marking.map ≫ f.curve.map = x.map) (c : ℂ)
    (v : Fiber (tangentSheaf P.structureMap) marking.map) :
    c • nodeDifferential f x hx v ∈ positiveNodeSpace f x hx :=
  (positiveNodeSpace f x hx).smul_mem c (nodeDifferential_mem_positiveNodeSpace f x hx v)

end LeBrunSalamon.Construction.Lines.ContactPositive

end

/-!
## Suitable-pair consumers using the proved contact-positive theorem

The variation constructor now uses the proved original node-space
horizontal containment. In complex dimension three the two actual
nonorthogonal curve tangents already belong to the positive spaces,
and intrinsic Levi alternation supplies the plane argument. Those old
extra membership and alternation premises are discharged here.

The source-specific variation maps and their surjectivity remain explicit
in the general constructor. The dimension-three result requires an actual
nonorthogonal pair of actual curves. No global suitable-pair existence
claim or new admission is introduced.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Lines.ContactPositive

section ActualVariation

variable {n : ℕ} {X : ContactFanoManifold n}
variable {A B : Type*} [AddCommGroup A] [Module ℂ A]
variable [AddCommGroup B] [Module ℂ B]

/-- Assemble the original SuitablePair from actual surjective variation.
The positive-space horizontality is proved by the new contact argument,
not imported from the historical admitted endpoint or old constructor. -/
def suitablePair_of_surjective_variation (x : ComplexPoint X.variety)
    (f g : FreeLine X) (hf : marking.map ≫ f.curve.map = x.map)
    (hg : marking.map ≫ g.curve.map = x.map)
    (p q : Fiber (tangentSheaf P.structureMap) marking.map)
    (htrans : NonzeroLeviPair X x (nodeDifferential f x hf p) (nodeDifferential g x hg q))
    (d₁ : A →ₗ[ℂ] contactPlane X x) (d₂ : B →ₗ[ℂ] contactPlane X x)
    (h₁ : ∀ a, (d₁ a : TangentFiber X.variety x) ∈ positiveNodeSpace f x hf)
    (h₂ : ∀ b, (d₂ b : TangentFiber X.variety x) ∈ positiveNodeSpace g x hg)
    (hsurj : Function.Surjective (d₁.coprod d₂)) : SuitablePair X where
  node := x
  first := f
  second := g
  firstAtNode := hf
  secondAtNode := hg
  firstParameter := p
  secondParameter := q
  firstParameter_ne := by
    intro hp
    apply SuitablePairAlgebra.nonzeroLeviPair_left_ne_zero X x htrans
    rw [hp, map_zero]
  secondParameter_ne := by
    intro hq
    apply SuitablePairAlgebra.nonzeroLeviPair_right_ne_zero X x htrans
    rw [hq, map_zero]
  spans := SuitablePairAlgebra.sup_eq_of_surjective_sum (contactPlane X x)
    (positiveNodeSpace f x hf) (positiveNodeSpace g x hg)
    (positiveNodeSpace_horizontal f x hf) (positiveNodeSpace_horizontal g x hg)
    d₁ d₂ h₁ h₂ hsurj
  transverse := htrans

end ActualVariation

/-- In complex dimension three, actual nonorthogonal curve tangents
give an original SuitablePair. Positive membership and intrinsic Levi
alternation are proved, so neither is an additional input. -/
def dimensionThree_suitablePair_of_tangents (X : ContactFanoManifold 1)
    (x : ComplexPoint X.variety) (f g : FreeLine X)
    (hf : marking.map ≫ f.curve.map = x.map)
    (hg : marking.map ≫ g.curve.map = x.map)
    (p q : Fiber (tangentSheaf P.structureMap) marking.map)
    (htrans : NonzeroLeviPair X x (nodeDifferential f x hf p) (nodeDifferential g x hg q)) :
    SuitablePair X := by
  letI : FiniteDimensional ℂ (TangentFiber X.variety x) :=
    fiber_finite (intrinsicTangentBundle X.variety) x.map
  let a : contactPlane X x :=
    ⟨nodeDifferential f x hf p, nodeDifferential_mem_contactPlane f x hf p⟩
  let b : contactPlane X x :=
    ⟨nodeDifferential g x hg q, nodeDifferential_mem_contactPlane g x hg q⟩
  have hab : SuitablePairAlgebra.contactLevi X x a b ≠ 0 :=
    (SuitablePairAlgebra.nonzeroLeviPair_iff_contactLevi X x a b).mp htrans
  have hdim : Module.finrank ℂ (contactPlane X x) = 2 := by
    simpa using contactPlane_dimension X x
  let d₁ := LinearMap.toSpanSingleton ℂ (contactPlane X x) a
  let d₂ := LinearMap.toSpanSingleton ℂ (contactPlane X x) b
  have h₁ : ∀ c : ℂ, (d₁ c : TangentFiber X.variety x) ∈ positiveNodeSpace f x hf := by
    intro c
    change c • nodeDifferential f x hf p ∈ positiveNodeSpace f x hf
    exact smul_nodeDifferential_mem_positiveNodeSpace f x hf c p
  have h₂ : ∀ c : ℂ, (d₂ c : TangentFiber X.variety x) ∈ positiveNodeSpace g x hg := by
    intro c
    change c • nodeDifferential g x hg q ∈ positiveNodeSpace g x hg
    exact smul_nodeDifferential_mem_positiveNodeSpace g x hg c q
  have hsurj : Function.Surjective (d₁.coprod d₂) :=
    (SuitablePairAlgebra.twoVectorSum_bijective hdim (SuitablePairAlgebra.contactLevi X x)
      (LeviFiberGeometry.contactLevi_alternating X x) hab).2
  exact suitablePair_of_surjective_variation x f g hf hg p q htrans d₁ d₂ h₁ h₂ hsurj

end LeBrunSalamon.Construction.Lines.ContactPositive

end

/-!
## The actual marked-value fiber of the rational Hom scheme

SOURCE: `lines:suitable-pair`, the fixed-node Hom family underlying variation
of curve velocity. All maps below are actual scheme pullbacks of the supplied
`HomSpacePresentation`. The parameter represents fixed-node families over
arbitrary test schemes, including nonreduced schemes. No tangent comparison,
smoothness, finite-type assertion, or velocity range statement is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.Skeleton

namespace LeBrunSalamon.Construction.Lines.FixedNodeHom

/-- The constant marked point in the actual product over the complex base. -/
def markingSection (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {T : Scheme} (sT : T ⟶ ComplexBase) : T ⟶ RationalSourceOver P T sT :=
  pullback.lift (sT ≫ p.map) (𝟙 T) (by simp [Category.assoc, p.overC])

@[simp] theorem markingSection_fst (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {T : Scheme} (sT : T ⟶ ComplexBase) :
    markingSection P p sT ≫ pullback.fst P.structureMap sT = sT ≫ p.map := by
  simp [markingSection]

@[simp] theorem markingSection_snd (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {T : Scheme} (sT : T ⟶ ComplexBase) :
    markingSection P p sT ≫ pullback.snd P.structureMap sT = 𝟙 T := by
  simp [markingSection]

/-- Changing the family parameter preserves the actual marked section. -/
theorem markingSection_naturality (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {T S : Scheme}
    {sT : T ⟶ ComplexBase} {sS : S ⟶ ComplexBase}
    (h : PointsOver T sT S sS) :
    markingSection P p sT ≫ rationalSourceMap P h =
      h.val ≫ markingSection P p sS := by
  apply pullback.hom_ext
  · simp only [Category.assoc, rationalSourceMap, pullback.lift_fst,
      markingSection_fst]
    rw [← Category.assoc, h.property]
  · simp only [Category.assoc, rationalSourceMap, pullback.lift_snd,
      markingSection_snd, Category.comp_id]
    rw [← Category.assoc, markingSection_snd, Category.id_comp]

/-- Evaluation at the specified marking on the universal rational family. -/
def markedEvaluation (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {d : ℕ} {X : SmoothProperComplexVariety d}
    (H : HomSpacePresentation P X) : H.parameter ⟶ X.scheme :=
  markingSection P p H.toC ≫ H.evaluation

theorem markedEvaluation_overC (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {d : ℕ} {X : SmoothProperComplexVariety d}
    (H : HomSpacePresentation P X) :
    markedEvaluation P p H ≫ X.structureMap = H.toC := by
  simp [markedEvaluation, Category.assoc, H.overC, markingSection, p.overC]

/-- The scheme-theoretic fiber of marked evaluation, without reduction. -/
abbrev parameter (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {d : ℕ} {X : SmoothProperComplexVariety d}
    (H : HomSpacePresentation P X) (x : ComplexPoint X) : Scheme :=
  pullback (markedEvaluation P p H) x.map

def toC (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {d : ℕ} {X : SmoothProperComplexVariety d}
    (H : HomSpacePresentation P X) (x : ComplexPoint X) :
    parameter P p H x ⟶ ComplexBase :=
  pullback.snd (markedEvaluation P p H) x.map

def inclusion (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {d : ℕ} {X : SmoothProperComplexVariety d}
    (H : HomSpacePresentation P X) (x : ComplexPoint X) :
    parameter P p H x ⟶ H.parameter :=
  pullback.fst (markedEvaluation P p H) x.map

theorem inclusion_overC (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {d : ℕ} {X : SmoothProperComplexVariety d}
    (H : HomSpacePresentation P X) (x : ComplexPoint X) :
    inclusion P p H x ≫ H.toC = toC P p H x := by
  have h := congrArg (fun k => k ≫ X.structureMap)
    (pullback.condition (f := markedEvaluation P p H) (g := x.map))
  simpa only [Category.assoc, markedEvaluation_overC, x.overC, Category.comp_id,
    inclusion, toC] using h

def asHomPoint (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {d : ℕ} {X : SmoothProperComplexVariety d}
    (H : HomSpacePresentation P X) (x : ComplexPoint X) :
    PointsOver (parameter P p H x) (toC P p H x) H.parameter H.toC :=
  ⟨inclusion P p H x, inclusion_overC P p H x⟩

/-- The universal evaluation restricted along its actual fixed-value fiber. -/
def evaluation (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {d : ℕ} {X : SmoothProperComplexVariety d}
    (H : HomSpacePresentation P X) (x : ComplexPoint X) :
    RationalSourceOver P (parameter P p H x) (toC P p H x) ⟶ X.scheme :=
  rationalSourceMap P (asHomPoint P p H x) ≫ H.evaluation

theorem evaluation_overC (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {d : ℕ} {X : SmoothProperComplexVariety d}
    (H : HomSpacePresentation P X) (x : ComplexPoint X) :
    evaluation P p H x ≫ X.structureMap =
      pullback.fst P.structureMap (toC P p H x) ≫ P.structureMap := by
  rw [evaluation, Category.assoc, H.overC, ← Category.assoc]
  congr 1
  exact pullback.lift_fst _ _ _

/-- The defining equation of the fixed-node family, as an equality of scheme
morphisms. It holds on the entire fiber, including all infinitesimal directions. -/
theorem fixedNode (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {d : ℕ} {X : SmoothProperComplexVariety d}
    (H : HomSpacePresentation P X) (x : ComplexPoint X) :
    markingSection P p (toC P p H x) ≫ evaluation P p H x =
      toC P p H x ≫ x.map := by
  have hn := congrArg (fun k => k ≫ H.evaluation)
    (markingSection_naturality P p (asHomPoint P p H x))
  have he : markingSection P p (toC P p H x) ≫ evaluation P p H x =
      inclusion P p H x ≫ markedEvaluation P p H := by
    simpa only [evaluation, asHomPoint, markedEvaluation, Category.assoc] using hn
  exact he.trans (pullback.condition (f := markedEvaluation P p H) (g := x.map))

/-- A test-family parameter satisfying the fixed-node equation lifts to the
actual fiber. The test scheme is unrestricted. -/
def lift (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {d : ℕ} {X : SmoothProperComplexVariety d}
    (H : HomSpacePresentation P X) (x : ComplexPoint X)
    {T : Scheme} {sT : T ⟶ ComplexBase}
    (h : PointsOver T sT H.parameter H.toC)
    (hx : h.val ≫ markedEvaluation P p H = sT ≫ x.map) :
    PointsOver T sT (parameter P p H x) (toC P p H x) :=
  ⟨pullback.lift h.val sT hx, by simp [toC]⟩

@[simp] theorem lift_inclusion (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {d : ℕ} {X : SmoothProperComplexVariety d}
    (H : HomSpacePresentation P X) (x : ComplexPoint X)
    {T : Scheme} {sT : T ⟶ ComplexBase}
    (h : PointsOver T sT H.parameter H.toC)
    (hx : h.val ≫ markedEvaluation P p H = sT ≫ x.map) :
    (lift P p H x h hx).val ≫ inclusion P p H x = h.val := by
  simp [lift, inclusion]

def forget (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {d : ℕ} {X : SmoothProperComplexVariety d}
    (H : HomSpacePresentation P X) (x : ComplexPoint X)
    {T : Scheme} {sT : T ⟶ ComplexBase}
    (h : PointsOver T sT (parameter P p H x) (toC P p H x)) :
    PointsOver T sT H.parameter H.toC :=
  ⟨h.val ≫ inclusion P p H x, by
    rw [Category.assoc, inclusion_overC, h.property]⟩

theorem forget_fixed (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {d : ℕ} {X : SmoothProperComplexVariety d}
    (H : HomSpacePresentation P X) (x : ComplexPoint X)
    {T : Scheme} {sT : T ⟶ ComplexBase}
    (h : PointsOver T sT (parameter P p H x) (toC P p H x)) :
    (forget P p H x h).val ≫ markedEvaluation P p H = sT ≫ x.map := by
  change (h.val ≫ inclusion P p H x) ≫ markedEvaluation P p H = sT ≫ x.map
  rw [Category.assoc]
  have hc : inclusion P p H x ≫ markedEvaluation P p H = toC P p H x ≫ x.map :=
    pullback.condition
  rw [hc, ← Category.assoc, h.property]

theorem forget_lift (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {d : ℕ} {X : SmoothProperComplexVariety d}
    (H : HomSpacePresentation P X) (x : ComplexPoint X)
    {T : Scheme} {sT : T ⟶ ComplexBase}
    (h : PointsOver T sT H.parameter H.toC)
    (hx : h.val ≫ markedEvaluation P p H = sT ≫ x.map) :
    forget P p H x (lift P p H x h hx) = h := by
  apply Subtype.ext
  exact lift_inclusion P p H x h hx

theorem lift_forget (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {d : ℕ} {X : SmoothProperComplexVariety d}
    (H : HomSpacePresentation P X) (x : ComplexPoint X)
    {T : Scheme} {sT : T ⟶ ComplexBase}
    (h : PointsOver T sT (parameter P p H x) (toC P p H x)) :
    lift P p H x (forget P p H x h) (forget_fixed P p H x h) = h := by
  apply Subtype.ext
  apply pullback.hom_ext
  · simp [lift, forget, inclusion]
  · simpa only [lift, pullback.lift_snd, toC] using h.property.symm

/-- The actual fiber has precisely the test points satisfying marked
incidence. This retains all nonreduced test schemes in the Hom contract. -/
def pointsEquiv (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {d : ℕ} {X : SmoothProperComplexVariety d}
    (H : HomSpacePresentation P X) (x : ComplexPoint X)
    (T : Scheme) (sT : T ⟶ ComplexBase) :
    PointsOver T sT (parameter P p H x) (toC P p H x) ≃
      {h : PointsOver T sT H.parameter H.toC //
        h.val ≫ markedEvaluation P p H = sT ≫ x.map} where
  toFun h := ⟨forget P p H x h, forget_fixed P p H x h⟩
  invFun h := lift P p H x h.val h.property
  left_inv := lift_forget P p H x
  right_inv h := by
    apply Subtype.ext
    exact forget_lift P p H x h.val h.property

end LeBrunSalamon.Construction.Lines.FixedNodeHom

end
