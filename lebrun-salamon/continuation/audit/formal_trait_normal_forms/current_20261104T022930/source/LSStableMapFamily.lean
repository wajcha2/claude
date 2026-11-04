import RecompileExtensionsPart04
import LSProjectivityDefinitions

/-!
# Scheme families underlying the stable-map compactification

All spaces and comparison morphisms in this file are actual schemes.
The two selected source points belong to the unmarked source, so its
whole fibre square is retained, including its diagonal and nodal points.

The structures below contain geometric family data only. In particular,
they contain no vector section, contact-order estimate, or extension
conclusion. The published existence input is reviewed separately.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseTwentyNine
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.PhaseThirtyFour LeBrunSalamon.Skeleton

namespace LeBrunSalamon.Construction.StableMaps

/-- The actual affine nodal model, with its actual coefficient map. -/
abbrev NodeScheme (R : CommRingCat) (a : R) : Scheme :=
  Spec (CommRingCat.of (NodeAlgebra R a))

def nodeProjection (R : CommRingCat) (a : R) : NodeScheme R a ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (algebraMap R (NodeAlgebra R a)))

/-- An étale local equation for the given morphism at the given point.
Both arrows to the base and the actual equation `uv = a` are retained.
This is the scheme-theoretic notion, not a label attached to a fibre. -/
structure EtaleNodeChart {C B : Scheme} (pi : C ⟶ B) (x : C) where
  baseRing : CommRingCat
  baseMap : Spec baseRing ⟶ B
  baseEtale : Etale baseMap
  parameter : baseRing
  chart : Scheme
  toSource : chart ⟶ C
  sourceEtale : Etale toSource
  toNode : chart ⟶ NodeScheme baseRing parameter
  nodeEtale : Etale toNode
  overBase : toSource ≫ pi = toNode ≫ nodeProjection baseRing parameter ≫ baseMap
  point : chart
  point_spec : toSource point = x

/-- A relative curve is nodal when every point has either a smooth
one-dimensional neighbourhood or the actual étale node presentation.
Flatness and finite presentation are stated separately on families. -/
def IsNodalCurve {C B : Scheme} (pi : C ⟶ B) : Prop :=
  ∀ x : C,
    (∃ U : C.Opens, x ∈ U ∧ SmoothOfRelativeDimension 1 (U.ι ≫ pi)) ∨
      Nonempty (EtaleNodeChart pi x)

/- IsProjectiveOver is imported from LSProjectivityDefinitions. -/

section GraphProofApplications

/- These local coercions expose the existing symmetry and irreflexivity
proofs as functions while preserving the original graph-field expressions. -/
local instance {V : Type*} {r : V → V → Prop} :
    CoeFun (Std.Symm r) (fun _ => ∀ {a b : V}, r a b → r b a) where
  coe h := fun {a b} hab => h.symm a b hab

local instance {V : Type*} {r : V → V → Prop} :
    CoeFun (Std.Irrefl r) (fun _ => ∀ a : V, ¬ r a a) where
  coe h := h.irrefl

/-- An actual unmarked genus-zero curve over C, given by its P1
components and the complete gluing universal property. Degree labels
are the degrees of the specified line on the actual components.

The positive number of components is `extraComponents + 1`. Distinct
flags at one component are distinct actual C-points. The universal
property is for maps to every scheme, not merely maps to the target. -/
structure StableTreePresentation (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) (Y : Scheme) (sY : Y ⟶ ComplexBase)
    (L : LineBundle Y) where
  extraComponents : ℕ
  tree : StableUnmarkedTree (V := Fin (extraComponents + 1))
  component : Fin (extraComponents + 1) → (ProjectiveLine ⟶ Y)
  componentClosed : ∀ v, IsClosedImmersion (component v)
  componentOverC : ∀ v, component v ≫ sY = P.structureMap
  node : ∀ v w, tree.graph.Adj v w → ProjectiveLinePoint P
  nodeDistinct : ∀ v w₁ w₂ (h₁ : tree.graph.Adj v w₁) (h₂ : tree.graph.Adj v w₂),
    w₁ ≠ w₂ → (node v w₁ h₁).map ≠ (node v w₂ h₂).map
  nodeIdentified : ∀ v w (h : tree.graph.Adj v w),
    (node v w h).map ≫ component v =
      (node w v (tree.graph.symm h)).map ≫ component w
  componentsCover : ∀ y : Y, ∃ v z, component v z = y
  gluing : ∀ (Z : Scheme) (a : Fin (extraComponents + 1) → (ProjectiveLine ⟶ Z)),
    (∀ v w (h : tree.graph.Adj v w),
      (node v w h).map ≫ a v = (node w v (tree.graph.symm h)).map ≫ a w) →
    ∃! f : Y ⟶ Z, ∀ v, component v ≫ f = a v
  degree : ∀ v, projectiveLineDegree P p (pullbackLine (component v) L) =
    (tree.degree v : ℤ)

namespace StableTreePresentation

variable {P : ProjectiveLineOverC} {p : ProjectiveLinePoint P}
variable {Y : Scheme} {sY : Y ⟶ ComplexBase} {L : LineBundle Y}
variable (T : StableTreePresentation P p Y sY L)

/-- The original finite-tree theorem now applies to degrees of actual
P1 component pullbacks. No geometric boundary conclusion is admitted. -/
theorem degreeTwo_classification (h : T.tree.totalDegree = 2) :
    (Fintype.card (Fin (T.extraComponents + 1)) = 1 ∧
      ∀ v, projectiveLineDegree P p (pullbackLine (T.component v) L) = 2) ∨
    (Fintype.card (Fin (T.extraComponents + 1)) = 2 ∧
      ∀ v, projectiveLineDegree P p (pullbackLine (T.component v) L) = 1) := by
  rcases stableDegreeTwoTree_classification T.tree h with h₁ | h₂
  · exact Or.inl ⟨h₁.1, fun v => by rw [T.degree v, h₁.2 v]; norm_num⟩
  · exact Or.inr ⟨h₂.1, fun v => by rw [T.degree v, h₂.2 v]; norm_num⟩

theorem degreeTwo_positive (h : T.tree.totalDegree = 2)
    (v : Fin (T.extraComponents + 1)) :
    0 < projectiveLineDegree P p (pullbackLine (T.component v) L) := by
  rw [T.degree v]
  exact_mod_cast stableDegreeTwoTree_noContracted T.tree h v

/-- Equality of actual maps is detected by the complete component
gluing. This will also be used to construct the one-component inverse. -/
theorem hom_ext {Z : Scheme} {f g : Y ⟶ Z}
    (h : ∀ v, T.component v ≫ f = T.component v ≫ g) : f = g := by
  let a := fun v => T.component v ≫ f
  have ha : ∀ v w (q : T.tree.graph.Adj v w),
      (T.node v w q).map ≫ a v =
        (T.node w v (T.tree.graph.symm q)).map ≫ a w := by
    intro v w q
    dsimp [a]
    rw [← Category.assoc, T.nodeIdentified v w q, Category.assoc]
  obtain ⟨k, hk, hu⟩ := T.gluing Z a ha
  exact (hu f (fun _ => rfl)).trans (hu g (fun v => (h v).symm)).symm

/-- A one-vertex presentation is an actual P1 isomorphism, proved
from its gluing universal property. -/
def oneComponentIso (h : Fintype.card (Fin (T.extraComponents + 1)) = 1)
    (v : Fin (T.extraComponents + 1)) : ProjectiveLine ≅ Y := by
  letI : Subsingleton (Fin (T.extraComponents + 1)) :=
    Fintype.card_le_one_iff_subsingleton.mp (by omega)
  have hcompat : ∀ a b (q : T.tree.graph.Adj a b),
      (T.node a b q).map ≫ (𝟙 ProjectiveLine) =
        (T.node b a (T.tree.graph.symm q)).map ≫ (𝟙 ProjectiveLine) := by
    intro a b q
    have hab : b = a := Subsingleton.elim b a
    subst b
    exact (T.tree.graph.loopless a q).elim
  let r := Classical.choose (T.gluing ProjectiveLine (fun _ => 𝟙 _) hcompat)
  have hr : ∀ w, T.component w ≫ r = 𝟙 ProjectiveLine :=
    (Classical.choose_spec (T.gluing ProjectiveLine (fun _ => 𝟙 _) hcompat)).1
  refine ⟨T.component v, r, hr v, ?_⟩
  apply T.hom_ext
  intro w
  rw [← Category.assoc, hr w]
  simpa only [Category.id_comp, Category.comp_id] using
    congrArg T.component (Subsingleton.elim v w)

/-- With two actual components the full tree gluing is exactly the
categorical pushout of their two node points. -/
theorem twoComponent_isPushout
    (v w : Fin (T.extraComponents + 1)) (hne : v ≠ w)
    (hall : ∀ u, u = v ∨ u = w) (hadj : T.tree.graph.Adj v w) :
    IsPushout (T.node v w hadj).map (T.node w v (T.tree.graph.symm hadj)).map
      (T.component v) (T.component w) := by
  classical
  apply IsPushout.mk' (T.nodeIdentified v w hadj)
  · intro Z f g hv hw
    apply T.hom_ext
    intro u
    rcases hall u with rfl | rfl
    · exact hv
    · exact hw
  · intro Z a b hab
    let c : Fin (T.extraComponents + 1) → (ProjectiveLine ⟶ Z) :=
      fun u => if u = v then a else b
    have hc : ∀ u z (h : T.tree.graph.Adj u z),
        (T.node u z h).map ≫ c u =
          (T.node z u (T.tree.graph.symm h)).map ≫ c z := by
      intro u z h
      rcases hall u with rfl | rfl <;> rcases hall z with rfl | rfl
      · exact (T.tree.graph.loopless _ h).elim
      · simpa only [c, if_pos rfl, if_neg hne.symm] using hab
      · simpa only [c, if_pos rfl, if_neg hne.symm] using hab.symm
      · exact (T.tree.graph.loopless _ h).elim
    obtain ⟨f, hf, _⟩ := T.gluing Z c hc
    exact ⟨f, by simpa only [c, if_pos rfl] using hf v,
      by simpa only [c, if_neg hne.symm] using hf w⟩

theorem twoComponent_nodes
    (h : Fintype.card (Fin (T.extraComponents + 1)) = 2) :
    ∃ v w : Fin (T.extraComponents + 1), v ≠ w ∧
      (∀ u, u = v ∨ u = w) ∧ T.tree.graph.Adj v w := by
  classical
  obtain ⟨v, w, hne, heq⟩ :=
    Finset.card_eq_two.mp (show (Finset.univ : Finset (Fin (T.extraComponents + 1))).card = 2
      from h)
  have hall (u : Fin (T.extraComponents + 1)) : u = v ∨ u = w := by
    have hu : u ∈ ({v, w} : Finset (Fin (T.extraComponents + 1))) :=
      heq ▸ Finset.mem_univ u
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hu
  letI : Nontrivial (Fin (T.extraComponents + 1)) := ⟨⟨v, w, hne⟩⟩
  obtain ⟨z, hz⟩ := T.tree.tree.preconnected.exists_adj_of_nontrivial v
  rcases hall z with hzv | hzw
  · exact (T.tree.graph.loopless v (hzv ▸ hz)).elim
  · exact ⟨v, w, hne, hall, hzw ▸ hz⟩

/-- The geometric degree-two alternative: either an actual P1
isomorphism, or two actual degree-one closed P1 components glued at
one actual pair of points. No contracted component remains. -/
theorem degreeTwo_presentation (h : T.tree.totalDegree = 2) :
    (∃ e : ProjectiveLine ≅ Y, e.hom ≫ sY = P.structureMap ∧
      projectiveLineDegree P p (pullbackLine e.hom L) = 2) ∨
    (∃ (i j : ProjectiveLine ⟶ Y) (a b : ProjectiveLinePoint P),
      IsClosedImmersion i ∧ IsClosedImmersion j ∧
      i ≫ sY = P.structureMap ∧ j ≫ sY = P.structureMap ∧
      IsPushout a.map b.map i j ∧
      projectiveLineDegree P p (pullbackLine i L) = 1 ∧
      projectiveLineDegree P p (pullbackLine j L) = 1) := by
  rcases T.degreeTwo_classification h with h₁ | h₂
  · let v : Fin (T.extraComponents + 1) := 0
    exact Or.inl ⟨T.oneComponentIso h₁.1 v, T.componentOverC v, h₁.2 v⟩
  · obtain ⟨v, w, hne, hall, hadj⟩ := T.twoComponent_nodes h₂.1
    exact Or.inr ⟨T.component v, T.component w,
      T.node v w hadj, T.node w v (T.tree.graph.symm hadj),
      T.componentClosed v, T.componentClosed w,
      T.componentOverC v, T.componentOverC w,
      T.twoComponent_isPushout v w hne hall hadj, h₂.2 v, h₂.2 w⟩

end StableTreePresentation

end GraphProofApplications

/-- A genuine projective family of unmarked stable genus-zero maps.
Nodality is imposed at all scheme points. Complex fibres additionally
carry the actual component/gluing data needed by the existing P1 API.
The dense open is a whole-source smooth locus, not merely a selection
of relatively smooth points on singular fibres. -/
structure ProjectiveNodalFamily (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {d : ℕ} (X : SmoothProperComplexVariety d)
    (L : LineBundle X.scheme) (degree : ℕ) where
  base : Scheme
  toC : base ⟶ ComplexBase
  baseProper : IsProper toC
  baseIntegral : IsIntegral base
  baseNormal : Descent.NormalScheme base
  source : Scheme
  parameter : source ⟶ base
  proper : IsProper parameter
  flat : Flat parameter
  finitePresentation : LocallyOfFinitePresentation parameter
  nodal : IsNodalCurve parameter
  projective : IsProjectiveOver parameter toC
  evaluation : source ⟶ X.scheme
  overC : evaluation ≫ X.structureMap = parameter ≫ toC
  smoothOpen : base.Opens
  smoothDense : Dense (smoothOpen : Set base)
  smooth : SmoothOfRelativeDimension 1 (pullback.snd parameter smoothOpen.ι)
  smoothGeometricallyIntegral : GeometricallyIntegral (pullback.snd parameter smoothOpen.ι)
  fibre : ∀ b : PointsOver ComplexBase (𝟙 ComplexBase) base toC,
    StableTreePresentation P p (pullback parameter b.val) (pullback.snd parameter b.val)
      (pullbackLine (pullback.fst parameter b.val ≫ evaluation) L)
  fibreDegree : ∀ b, (fibre b).tree.totalDegree = degree

/-- The scheme base-change of a finite stable-stack cover to a full
Hom open. The source isomorphism identifies the actual universal maps.
Its smooth surjection to the chosen base open also supplies genuine
local P1 parametrizations for descent of invariant source tensors. -/
structure FullHomComparison (P : ProjectiveLineOverC)
    (p : ProjectiveLinePoint P) {d : ℕ} (X : SmoothProperComplexVariety d)
    (H : HomSpacePresentation P X) (U : H.parameter.Opens)
    (L : LineBundle X.scheme) (degree : ℕ)
    (F : ProjectiveNodalFamily P p X L degree) where
  cover : Scheme
  toHom : cover ⟶ U.toScheme
  finite : IsFinite toHom
  surjective : Surjective toHom
  toSmooth : cover ⟶ F.smoothOpen.toScheme
  smooth : Smooth toSmooth
  smoothSurjective : Surjective toSmooth
  geometricallyIntegral : GeometricallyIntegral toSmooth
  overC : (toSmooth ≫ F.smoothOpen.ι) ≫ F.toC = toHom ≫ U.ι ≫ H.toC
  sourceIso : RationalSourceOver P cover (toHom ≫ U.ι ≫ H.toC) ≅
    pullback F.parameter (toSmooth ≫ F.smoothOpen.ι)
  sourceOverBase : sourceIso.hom ≫
    pullback.snd F.parameter (toSmooth ≫ F.smoothOpen.ι) =
      pullback.snd P.structureMap (toHom ≫ U.ι ≫ H.toC)
  evaluation : sourceIso.hom ≫
    pullback.fst F.parameter (toSmooth ≫ F.smoothOpen.ι) ≫ F.evaluation =
      rationalSourceMap P
        (⟨toHom ≫ U.ι, rfl⟩ :
          PointsOver cover (toHom ≫ U.ι ≫ H.toC) H.parameter H.toC) ≫ H.evaluation

namespace ProjectiveNodalFamily

variable {P : ProjectiveLineOverC} {p : ProjectiveLinePoint P}
variable {d : ℕ} {X : SmoothProperComplexVariety d}
variable {L : LineBundle X.scheme} {degree : ℕ}
variable (F : ProjectiveNodalFamily P p X L degree)

/-- The actual relative square, without removal of the diagonal or
normalization of its total space. -/
abbrev Square : Scheme := pullback F.parameter F.parameter

def squareToBase : F.Square ⟶ F.base :=
  pullback.fst F.parameter F.parameter ≫ F.parameter

abbrev smoothSquareOpen : F.Square.Opens := F.squareToBase ⁻¹ᵁ F.smoothOpen

abbrev smoothSquareParameter : F.smoothSquareOpen.toScheme ⟶ F.smoothOpen.toScheme :=
  F.squareToBase ∣_ F.smoothOpen

def squareEvaluation : F.Square ⟶ SelfProduct X.structureMap :=
  pullback.lift
    (pullback.fst F.parameter F.parameter ≫ F.evaluation)
    (pullback.snd F.parameter F.parameter ≫ F.evaluation) (by
      simp only [Category.assoc, F.overC]
      simpa only [Category.assoc] using congrArg (fun q => q ≫ F.toC)
        (pullback.condition (f := F.parameter) (g := F.parameter)))

@[reassoc] theorem squareEvaluation_first :
    F.squareEvaluation ≫ firstProjection X.structureMap =
      pullback.fst F.parameter F.parameter ≫ F.evaluation :=
  pullback.lift_fst _ _ _

@[reassoc] theorem squareEvaluation_second :
    F.squareEvaluation ≫ secondProjection X.structureMap =
      pullback.snd F.parameter F.parameter ≫ F.evaluation :=
  pullback.lift_snd _ _ _

@[reassoc] theorem squareEvaluation_toC :
    F.squareEvaluation ≫ firstProjection X.structureMap ≫ X.structureMap =
      F.squareToBase ≫ F.toC := by
  rw [F.squareEvaluation_first_assoc, F.overC]
  simp only [squareToBase, Category.assoc]

theorem squareToBase_proper : IsProper F.squareToBase := by
  letI : IsProper F.parameter := F.proper
  change IsProper (pullback.fst F.parameter F.parameter ≫ F.parameter)
  infer_instance

/-- Properness belongs to the actual whole relative source square.
It is not obtained by replacing that square with a normalization. -/
theorem squareEvaluation_proper : IsProper F.squareEvaluation := by
  letI : IsProper F.squareToBase := F.squareToBase_proper
  letI : IsProper F.toC := F.baseProper
  letI : IsProper (F.squareEvaluation ≫
      (firstProjection X.structureMap ≫ X.structureMap)) := by
    rw [F.squareEvaluation_toC]
    infer_instance
  exact IsProper.of_comp F.squareEvaluation
    (firstProjection X.structureMap ≫ X.structureMap)

theorem base_locallyNoetherian : IsLocallyNoetherian F.base := by
  letI : IsProper F.toC := F.baseProper
  exact LocallyOfFiniteType.isLocallyNoetherian F.toC

theorem square_locallyNoetherian : IsLocallyNoetherian F.Square := by
  letI : IsProper F.toC := F.baseProper
  letI : IsProper F.squareToBase := F.squareToBase_proper
  exact LocallyOfFiniteType.isLocallyNoetherian (F.squareToBase ≫ F.toC)

theorem square_noetherianOnAffines : NormalExtension.NoetherianOnAffines F.Square := by
  letI : IsLocallyNoetherian F.Square := F.square_locallyNoetherian
  intro U hU
  exact IsLocallyNoetherian.component_noetherian ⟨U, hU⟩

end ProjectiveNodalFamily

namespace FullHomComparison

variable {P : ProjectiveLineOverC} {p : ProjectiveLinePoint P}
variable {d : ℕ} {X : SmoothProperComplexVariety d}
variable {H : HomSpacePresentation P X} {U : H.parameter.Opens}
variable {L : LineBundle X.scheme} {degree : ℕ}
variable {F : ProjectiveNodalFamily P p X L degree}
variable (Q : FullHomComparison P p X H U L degree F)

abbrev coverToC : Q.cover ⟶ ComplexBase := Q.toHom ≫ U.ι ≫ H.toC

abbrev coverToBase : Q.cover ⟶ F.base := Q.toSmooth ≫ F.smoothOpen.ι

def sourceMap : RationalSourceOver P Q.cover Q.coverToC ⟶ F.source :=
  Q.sourceIso.hom ≫ pullback.fst F.parameter Q.coverToBase

@[reassoc] theorem sourceMap_parameter :
    Q.sourceMap ≫ F.parameter =
      pullback.snd P.structureMap Q.coverToC ≫ Q.coverToBase := by
  dsimp [sourceMap]
  rw [Category.assoc, pullback.condition, ← Category.assoc, Q.sourceOverBase]

@[reassoc] theorem sourceMap_evaluation :
    Q.sourceMap ≫ F.evaluation =
      rationalSourceMap P
        (⟨Q.toHom ≫ U.ι, rfl⟩ : PointsOver Q.cover Q.coverToC H.parameter H.toC) ≫
          H.evaluation := Q.evaluation

abbrev parametrizedSource : Scheme := RationalSourceOver P Q.cover Q.coverToC

abbrev parametrizedParameter : Q.parametrizedSource ⟶ Q.cover :=
  pullback.snd P.structureMap Q.coverToC

theorem sourceMap_isPullback :
    IsPullback Q.sourceMap Q.parametrizedParameter F.parameter Q.coverToBase := by
  apply (IsPullback.of_hasPullback F.parameter Q.coverToBase).of_iso'
    Q.sourceIso (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [sourceMap, Iso.refl_hom, Category.comp_id]
  · simpa only [Iso.refl_hom, Category.comp_id] using Q.sourceOverBase
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

def complexSourceInclusion
    (q : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC) :
    ProjectiveLine ⟶ Q.parametrizedSource :=
  pullback.lift (𝟙 ProjectiveLine) (P.structureMap ≫ q.val) (by
    simp only [Category.id_comp, Category.assoc, q.property, Category.comp_id])

def complexSourceMap
    (q : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC) :
    ProjectiveLine ⟶ F.source := Q.complexSourceInclusion q ≫ Q.sourceMap

@[reassoc] theorem complexSourceMap_parameter
    (q : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC) :
    Q.complexSourceMap q ≫ F.parameter = P.structureMap ≫ q.val ≫ Q.coverToBase := by
  simp only [complexSourceMap, Category.assoc, Q.sourceMap_parameter,
    complexSourceInclusion, pullback.lift_snd_assoc, Category.assoc]

def complexFibreMap
    (q : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC) :
    ProjectiveLine ⟶ pullback F.parameter (q.val ≫ Q.coverToBase) :=
  pullback.lift (Q.complexSourceMap q) P.structureMap (Q.complexSourceMap_parameter q)

def complexFibreLift
    (q : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC) :
    pullback F.parameter (q.val ≫ Q.coverToBase) ⟶ Q.parametrizedSource :=
  Q.sourceMap_isPullback.lift (pullback.fst F.parameter (q.val ≫ Q.coverToBase))
    (pullback.snd F.parameter (q.val ≫ Q.coverToBase) ≫ q.val) (by
      simpa only [Category.assoc] using
        (pullback.condition (f := F.parameter) (g := q.val ≫ Q.coverToBase)))

@[reassoc] theorem complexFibreLift_source
    (q : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC) :
    Q.complexFibreLift q ≫ Q.sourceMap =
      pullback.fst F.parameter (q.val ≫ Q.coverToBase) :=
  IsPullback.lift_fst _ _ _ _

@[reassoc] theorem complexFibreLift_parameter
    (q : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC) :
    Q.complexFibreLift q ≫ Q.parametrizedParameter =
      pullback.snd F.parameter (q.val ≫ Q.coverToBase) ≫ q.val :=
  IsPullback.lift_snd _ _ _ _

def complexFibreInverse
    (q : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC) :
    pullback F.parameter (q.val ≫ Q.coverToBase) ⟶ ProjectiveLine :=
  Q.complexFibreLift q ≫ pullback.fst P.structureMap Q.coverToC

@[reassoc] theorem complexFibreInverse_toC
    (q : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC) :
    Q.complexFibreInverse q ≫ P.structureMap =
      pullback.snd F.parameter (q.val ≫ Q.coverToBase) := by
  calc
    Q.complexFibreInverse q ≫ P.structureMap =
        Q.complexFibreLift q ≫
          (pullback.fst P.structureMap Q.coverToC ≫ P.structureMap) :=
      Category.assoc _ _ _
    _ = Q.complexFibreLift q ≫
        (pullback.snd P.structureMap Q.coverToC ≫ Q.coverToC) :=
      congrArg (fun k : Q.parametrizedSource ⟶ ComplexBase =>
        Q.complexFibreLift q ≫ k)
        (pullback.condition (f := P.structureMap) (g := Q.coverToC))
    _ = (Q.complexFibreLift q ≫ Q.parametrizedParameter) ≫ Q.coverToC :=
      (Category.assoc _ _ _).symm
    _ = (pullback.snd F.parameter (q.val ≫ Q.coverToBase) ≫ q.val) ≫
        Q.coverToC :=
      congrArg
        (fun k : pullback F.parameter (q.val ≫ Q.coverToBase) ⟶ Q.cover =>
          k ≫ Q.coverToC) (Q.complexFibreLift_parameter q)
    _ = pullback.snd F.parameter (q.val ≫ Q.coverToBase) ≫
        (q.val ≫ Q.coverToC) := Category.assoc _ _ _
    _ = pullback.snd F.parameter (q.val ≫ Q.coverToBase) ≫ 𝟙 ComplexBase :=
      congrArg (fun k : ComplexBase ⟶ ComplexBase =>
        pullback.snd F.parameter (q.val ≫ Q.coverToBase) ≫ k) q.property
    _ = pullback.snd F.parameter (q.val ≫ Q.coverToBase) := Category.comp_id _

@[reassoc] theorem complexFibreInverse_inclusion
    (q : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC) :
    Q.complexFibreInverse q ≫ Q.complexSourceInclusion q = Q.complexFibreLift q := by
  apply pullback.hom_ext
  · simp only [Category.assoc, complexSourceInclusion, pullback.lift_fst,
      Category.comp_id, complexFibreInverse]
  · simp only [Category.assoc, complexSourceInclusion, pullback.lift_snd]
    calc
      Q.complexFibreInverse q ≫ P.structureMap ≫ q.val =
          (Q.complexFibreInverse q ≫ P.structureMap) ≫ q.val :=
        (Category.assoc _ _ _).symm
      _ = pullback.snd F.parameter (q.val ≫ Q.coverToBase) ≫ q.val :=
        congrArg
          (fun k : pullback F.parameter (q.val ≫ Q.coverToBase) ⟶ ComplexBase =>
            k ≫ q.val) (Q.complexFibreInverse_toC q)
      _ = Q.complexFibreLift q ≫ pullback.snd P.structureMap Q.coverToC :=
        (Q.complexFibreLift_parameter q).symm

@[reassoc] theorem complexFibreMap_lift
    (q : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC) :
    Q.complexFibreMap q ≫ Q.complexFibreLift q = Q.complexSourceInclusion q := by
  apply Q.sourceMap_isPullback.hom_ext
  · simp only [Category.assoc, Q.complexFibreLift_source,
      complexFibreMap, pullback.lift_fst, complexSourceMap]
  · simp only [Category.assoc, Q.complexFibreLift_parameter,
      complexFibreMap, pullback.lift_snd_assoc, complexSourceInclusion,
      pullback.lift_snd]

/-- Every actual complex point of the cover gives an actual P1
isomorphism onto its entire source fibre, with both projections fixed. -/
def complexFibreIso
    (q : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC) :
    ProjectiveLine ≅ pullback F.parameter (q.val ≫ Q.coverToBase) where
  hom := Q.complexFibreMap q
  inv := Q.complexFibreInverse q
  hom_inv_id := by
    rw [complexFibreInverse, ← Category.assoc, Q.complexFibreMap_lift]
    exact pullback.lift_fst _ _ _
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [complexFibreMap, Category.assoc, pullback.lift_fst,
        Category.id_comp, complexSourceMap]
      calc
        Q.complexFibreInverse q ≫ Q.complexSourceInclusion q ≫ Q.sourceMap =
            (Q.complexFibreInverse q ≫ Q.complexSourceInclusion q) ≫ Q.sourceMap :=
          (Category.assoc _ _ _).symm
        _ = Q.complexFibreLift q ≫ Q.sourceMap :=
          congrArg
            (fun k : pullback F.parameter (q.val ≫ Q.coverToBase) ⟶
                Q.parametrizedSource => k ≫ Q.sourceMap)
            (Q.complexFibreInverse_inclusion q)
        _ = pullback.fst F.parameter (q.val ≫ Q.coverToBase) :=
          Q.complexFibreLift_source q
    · simp only [complexFibreMap, Category.assoc, pullback.lift_snd,
        Category.id_comp, Q.complexFibreInverse_toC]

@[reassoc] theorem complexFibreIso_source
    (q : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC) :
    (Q.complexFibreIso q).hom ≫ pullback.fst F.parameter (q.val ≫ Q.coverToBase) =
      Q.complexSourceMap q := pullback.lift_fst _ _ _

@[reassoc] theorem complexFibreIso_toC
    (q : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC) :
    (Q.complexFibreIso q).hom ≫ pullback.snd F.parameter (q.val ≫ Q.coverToBase) =
      P.structureMap := pullback.lift_snd _ _ _

def complexHomPoint
    (q : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC) :
    PointsOver ComplexBase (𝟙 ComplexBase) H.parameter H.toC :=
  ⟨q.val ≫ Q.toHom ≫ U.ι, by simpa only [coverToC, Category.assoc] using q.property⟩

@[reassoc] theorem complexSourceMap_evaluation
    (q : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC) :
    Q.complexSourceMap q ≫ F.evaluation = H.mapAt P (Q.complexHomPoint q) := by
  rw [complexSourceMap, Category.assoc, Q.sourceMap_evaluation]
  dsimp only [HomSpacePresentation.mapAt]
  simp only [← Category.assoc]
  apply congrArg (fun k => k ≫ H.evaluation)
  apply pullback.hom_ext
  · simp only [Category.assoc, rationalSourceMap, complexSourceInclusion,
      pullback.lift_fst_assoc, pullback.lift_fst, Category.comp_id]
  · simp only [Category.assoc, rationalSourceMap, complexSourceInclusion,
      complexHomPoint, pullback.lift_snd_assoc, pullback.lift_snd]

@[reassoc] theorem complexFibreIso_evaluation
    (q : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC) :
    (Q.complexFibreIso q).hom ≫ pullback.fst F.parameter (q.val ≫ Q.coverToBase) ≫
      F.evaluation = H.mapAt P (Q.complexHomPoint q) := by
  rw [← Category.assoc, Q.complexFibreIso_source, Q.complexSourceMap_evaluation]

def complexTransition
    (q₀ q₁ : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC)
    (h : q₀.val ≫ Q.coverToBase = q₁.val ≫ Q.coverToBase) :
    ProjectiveLine ≅ ProjectiveLine :=
  Q.complexFibreIso q₀ ≪≫ pullback.congrHom rfl h ≪≫ (Q.complexFibreIso q₁).symm

@[reassoc] theorem complexTransition_fibre
    (q₀ q₁ : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC)
    (h : q₀.val ≫ Q.coverToBase = q₁.val ≫ Q.coverToBase) :
    (Q.complexTransition q₀ q₁ h).hom ≫ (Q.complexFibreIso q₁).hom =
      (Q.complexFibreIso q₀).hom ≫ (pullback.congrHom rfl h).hom := by
  simp only [complexTransition, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

@[reassoc] theorem complexTransition_source
    (q₀ q₁ : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC)
    (h : q₀.val ≫ Q.coverToBase = q₁.val ≫ Q.coverToBase) :
    (Q.complexTransition q₀ q₁ h).hom ≫ Q.complexSourceMap q₁ =
      Q.complexSourceMap q₀ := by
  rw [← Q.complexFibreIso_source q₁, ← Category.assoc, Q.complexTransition_fibre]
  simp only [Category.assoc, pullback.congrHom_hom, pullback.map,
    pullback.lift_fst, Category.comp_id, Q.complexFibreIso_source]

@[reassoc] theorem complexTransition_overC
    (q₀ q₁ : PointsOver ComplexBase (𝟙 ComplexBase) Q.cover Q.coverToC)
    (h : q₀.val ≫ Q.coverToBase = q₁.val ≫ Q.coverToBase) :
    (Q.complexTransition q₀ q₁ h).hom ≫ P.structureMap = P.structureMap := by
  rw [← Q.complexFibreIso_toC q₁, ← Category.assoc, Q.complexTransition_fibre]
  simp only [Category.assoc, pullback.congrHom_hom, pullback.map,
    pullback.lift_snd, Category.comp_id, Q.complexFibreIso_toC]

/-- The entire square of the actual P1 family over the finite cover. -/
abbrev ParametrizedSquare : Scheme :=
  pullback Q.parametrizedParameter Q.parametrizedParameter

abbrev parametrizedSquareToCover : Q.ParametrizedSquare ⟶ Q.cover :=
  pullback.fst Q.parametrizedParameter Q.parametrizedParameter ≫ Q.parametrizedParameter

@[reassoc] theorem parametrizedSquare_second_parameter :
    pullback.snd Q.parametrizedParameter Q.parametrizedParameter ≫
      Q.parametrizedParameter = Q.parametrizedSquareToCover :=
  pullback.condition.symm

def parametrizedSquareToFamily : Q.ParametrizedSquare ⟶ F.Square :=
  pullback.lift
    (pullback.fst Q.parametrizedParameter Q.parametrizedParameter ≫ Q.sourceMap)
    (pullback.snd Q.parametrizedParameter Q.parametrizedParameter ≫ Q.sourceMap) (by
      simp only [Category.assoc, Q.sourceMap_parameter]
      simpa only [Category.assoc] using congrArg (fun k => k ≫ Q.coverToBase)
        (pullback.condition (f := Q.parametrizedParameter) (g := Q.parametrizedParameter)))

@[reassoc] theorem parametrizedSquareToFamily_first :
    Q.parametrizedSquareToFamily ≫ pullback.fst F.parameter F.parameter =
      pullback.fst Q.parametrizedParameter Q.parametrizedParameter ≫ Q.sourceMap :=
  pullback.lift_fst _ _ _

@[reassoc] theorem parametrizedSquareToFamily_second :
    Q.parametrizedSquareToFamily ≫ pullback.snd F.parameter F.parameter =
      pullback.snd Q.parametrizedParameter Q.parametrizedParameter ≫ Q.sourceMap :=
  pullback.lift_snd _ _ _

@[reassoc] theorem parametrizedSquareToFamily_base :
    Q.parametrizedSquareToFamily ≫ F.squareToBase =
      Q.parametrizedSquareToCover ≫ Q.coverToBase := by
  change Q.parametrizedSquareToFamily ≫
    (pullback.fst F.parameter F.parameter ≫ F.parameter) = _
  rw [← Category.assoc, Q.parametrizedSquareToFamily_first,
    Category.assoc, Q.sourceMap_parameter]
  simp only [parametrizedSquareToCover, Category.assoc]

/-- Formation of the complete source square commutes with the actual
source-family base change. Both its existence and uniqueness use the
given source isomorphism, rather than a set-theoretic parametrization. -/
theorem parametrizedSquareToFamily_isPullback :
    IsPullback Q.parametrizedSquareToFamily Q.parametrizedSquareToCover
      F.squareToBase Q.coverToBase := by
  apply IsPullback.mk' Q.parametrizedSquareToFamily_base
  · intro T a b ha hb
    apply pullback.hom_ext
    · apply Q.sourceMap_isPullback.hom_ext
      · simpa only [Category.assoc, Q.parametrizedSquareToFamily_first] using
          congrArg (fun k => k ≫ pullback.fst F.parameter F.parameter) ha
      · simpa only [parametrizedSquareToCover, Category.assoc] using hb
    · apply Q.sourceMap_isPullback.hom_ext
      · simpa only [Category.assoc, Q.parametrizedSquareToFamily_second] using
          congrArg (fun k => k ≫ pullback.snd F.parameter F.parameter) ha
      · simpa only [Category.assoc, Q.parametrizedSquare_second_parameter] using hb
  · intro T a b hab
    have ha₁ : (a ≫ pullback.fst F.parameter F.parameter) ≫ F.parameter =
        b ≫ Q.coverToBase := by
      simpa only [ProjectiveNodalFamily.squareToBase, Category.assoc] using hab
    have ha₂ : (a ≫ pullback.snd F.parameter F.parameter) ≫ F.parameter =
        b ≫ Q.coverToBase := by
      rw [Category.assoc, ← pullback.condition]
      simpa only [Category.assoc] using ha₁
    let l₁ := Q.sourceMap_isPullback.lift
      (a ≫ pullback.fst F.parameter F.parameter) b ha₁
    let l₂ := Q.sourceMap_isPullback.lift
      (a ≫ pullback.snd F.parameter F.parameter) b ha₂
    let l : T ⟶ Q.ParametrizedSquare := pullback.lift l₁ l₂ (by
      simp only [l₁, l₂, IsPullback.lift_snd])
    refine ⟨l, ?_, ?_⟩
    · apply pullback.hom_ext
      · simp only [l, Category.assoc, Q.parametrizedSquareToFamily_first,
          pullback.lift_fst_assoc, l₁, IsPullback.lift_fst]
      · simp only [l, Category.assoc, Q.parametrizedSquareToFamily_second,
          pullback.lift_snd_assoc, l₂, IsPullback.lift_fst]
    · simp only [l, parametrizedSquareToCover, Category.assoc,
        pullback.lift_fst_assoc, l₁, IsPullback.lift_snd]

def parametrizedSquareToSmooth : Q.ParametrizedSquare ⟶ F.smoothSquareOpen.toScheme :=
  (isPullback_morphismRestrict F.squareToBase F.smoothOpen).lift
    (Q.parametrizedSquareToCover ≫ Q.toSmooth) Q.parametrizedSquareToFamily (by
      simpa only [coverToBase, Category.assoc] using Q.parametrizedSquareToFamily_base.symm)

@[reassoc] theorem parametrizedSquareToSmooth_ι :
    Q.parametrizedSquareToSmooth ≫ F.smoothSquareOpen.ι =
      Q.parametrizedSquareToFamily :=
  IsPullback.lift_snd _ _ _ _

@[reassoc] theorem parametrizedSquareToSmooth_base :
    Q.parametrizedSquareToSmooth ≫ F.smoothSquareParameter =
      Q.parametrizedSquareToCover ≫ Q.toSmooth :=
  IsPullback.lift_fst _ _ _ _

theorem parametrizedSquareToSmooth_isPullback :
    IsPullback Q.parametrizedSquareToSmooth Q.parametrizedSquareToCover
      F.smoothSquareParameter Q.toSmooth := by
  apply IsPullback.of_right
    (t := (isPullback_morphismRestrict F.squareToBase F.smoothOpen).flip)
  · simpa only [Q.parametrizedSquareToSmooth_ι, coverToBase] using
      Q.parametrizedSquareToFamily_isPullback
  · exact Q.parametrizedSquareToSmooth_base

theorem parametrizedSquareToSmooth_smooth : Smooth Q.parametrizedSquareToSmooth :=
  MorphismProperty.of_isPullback Q.parametrizedSquareToSmooth_isPullback.flip Q.smooth

theorem parametrizedSquareToSmooth_surjective : Surjective Q.parametrizedSquareToSmooth :=
  MorphismProperty.of_isPullback Q.parametrizedSquareToSmooth_isPullback.flip Q.smoothSurjective

theorem parametrizedSquareToSmooth_geometricallyIntegral :
    GeometricallyIntegral Q.parametrizedSquareToSmooth :=
  MorphismProperty.of_isPullback Q.parametrizedSquareToSmooth_isPullback.flip
    Q.geometricallyIntegral

open LeBrunSalamon.Refinement.HomTwoPointEvaluation in
/-- The finite cover after base change to the universal pair of source
points over the entire chosen Hom neighbourhood. -/
abbrev UniversalCover : Scheme :=
  pullback Q.toHom (pullback.snd (squareStructure P) (U.ι ≫ H.toC))

open LeBrunSalamon.Refinement.HomTwoPointEvaluation in
abbrev universalToHomSource : Q.UniversalCover ⟶ Source P H U :=
  pullback.snd Q.toHom (pullback.snd (squareStructure P) (U.ι ≫ H.toC))

open LeBrunSalamon.Refinement.HomTwoPointEvaluation in
abbrev universalToCover : Q.UniversalCover ⟶ Q.cover :=
  pullback.fst Q.toHom (pullback.snd (squareStructure P) (U.ι ≫ H.toC))

open LeBrunSalamon.Refinement.HomTwoPointEvaluation in
abbrev universalToSourceSquare : Q.UniversalCover ⟶ SelfProduct P.structureMap :=
  Q.universalToHomSource ≫ pullback.fst (squareStructure P) (U.ι ≫ H.toC)

theorem universalToHomSource_finite : IsFinite Q.universalToHomSource := by
  letI : IsFinite Q.toHom := Q.finite
  exact inferInstance

theorem universalToHomSource_surjective : Function.Surjective Q.universalToHomSource := by
  letI : Surjective Q.toHom := Q.surjective
  exact Q.universalToHomSource.surjective

open LeBrunSalamon.Refinement.HomTwoPointEvaluation in
@[reassoc] theorem universal_parameter :
    Q.universalToCover ≫ Q.toHom =
      Q.universalToHomSource ≫ pullback.snd (squareStructure P) (U.ι ≫ H.toC) :=
  pullback.condition

open LeBrunSalamon.Refinement.HomTwoPointEvaluation in
theorem universal_first_overC :
    (Q.universalToSourceSquare ≫ firstProjection P.structureMap) ≫ P.structureMap =
      Q.universalToCover ≫ Q.coverToC := by
  have h₁ := congrArg (fun k => Q.universalToHomSource ≫ k)
    (pullback.condition (f := squareStructure P) (g := U.ι ≫ H.toC))
  have h₂ := congrArg (fun k => k ≫ U.ι ≫ H.toC) Q.universal_parameter
  calc
    (Q.universalToSourceSquare ≫ firstProjection P.structureMap) ≫ P.structureMap =
        (Q.universalToHomSource ≫
          pullback.snd (squareStructure P) (U.ι ≫ H.toC)) ≫ U.ι ≫ H.toC := by
      simpa only [universalToSourceSquare, squareStructure, Category.assoc] using h₁
    _ = Q.universalToCover ≫ Q.coverToC := by
      simpa only [coverToC, Category.assoc] using h₂.symm

theorem universal_second_overC :
    (Q.universalToSourceSquare ≫ secondProjection P.structureMap) ≫ P.structureMap =
      Q.universalToCover ≫ Q.coverToC := by
  rw [Category.assoc, ← pullback.condition]
  simpa only [Category.assoc] using Q.universal_first_overC

def universalFirst : Q.UniversalCover ⟶ F.source :=
  pullback.lift (Q.universalToSourceSquare ≫ firstProjection P.structureMap)
    Q.universalToCover Q.universal_first_overC ≫ Q.sourceMap

def universalSecond : Q.UniversalCover ⟶ F.source :=
  pullback.lift (Q.universalToSourceSquare ≫ secondProjection P.structureMap)
    Q.universalToCover Q.universal_second_overC ≫ Q.sourceMap

@[reassoc] theorem universalFirst_parameter :
    Q.universalFirst ≫ F.parameter = Q.universalToCover ≫ Q.coverToBase := by
  simp only [universalFirst, Category.assoc, Q.sourceMap_parameter,
    pullback.lift_snd_assoc]

@[reassoc] theorem universalSecond_parameter :
    Q.universalSecond ≫ F.parameter = Q.universalToCover ≫ Q.coverToBase := by
  simp only [universalSecond, Category.assoc, Q.sourceMap_parameter,
    pullback.lift_snd_assoc]

def universalToFamilySquare : Q.UniversalCover ⟶ F.Square :=
  pullback.lift Q.universalFirst Q.universalSecond
    (Q.universalFirst_parameter.trans Q.universalSecond_parameter.symm)

open LeBrunSalamon.Refinement.HomTwoPointEvaluation in
@[reassoc] theorem universalFirst_evaluation :
    Q.universalFirst ≫ F.evaluation =
      Q.universalToHomSource ≫ leftSource P H U ≫ H.evaluation := by
  simp only [universalFirst, Category.assoc, Q.sourceMap_evaluation]
  simp only [← Category.assoc]
  apply congrArg (fun k => k ≫ H.evaluation)
  apply pullback.hom_ext
  · simp only [rationalSourceMap, leftSource, Category.assoc,
      pullback.lift_fst_assoc, pullback.lift_fst, Category.comp_id,
      universalToSourceSquare]
  · simp only [rationalSourceMap, leftSource, Category.assoc,
      pullback.lift_snd_assoc, pullback.lift_snd]
    simpa only [Category.assoc] using congrArg (fun k => k ≫ U.ι) Q.universal_parameter

open LeBrunSalamon.Refinement.HomTwoPointEvaluation in
@[reassoc] theorem universalSecond_evaluation :
    Q.universalSecond ≫ F.evaluation =
      Q.universalToHomSource ≫ rightSource P H U ≫ H.evaluation := by
  simp only [universalSecond, Category.assoc, Q.sourceMap_evaluation]
  simp only [← Category.assoc]
  apply congrArg (fun k => k ≫ H.evaluation)
  apply pullback.hom_ext
  · simp only [rationalSourceMap, rightSource, Category.assoc,
      pullback.lift_fst_assoc, pullback.lift_fst, Category.comp_id,
      universalToSourceSquare]
  · simp only [rationalSourceMap, rightSource, Category.assoc,
      pullback.lift_snd_assoc, pullback.lift_snd]
    simpa only [Category.assoc] using congrArg (fun k => k ≫ U.ι) Q.universal_parameter

section HomTwoPointEvaluationNames

-- The structure field with this short name is a different map.
local notation "evaluation" => LeBrunSalamon.Refinement.HomTwoPointEvaluation.evaluation

open LeBrunSalamon.Refinement.HomTwoPointEvaluation in
/-- The compactified square evaluation restricts to the original
universal two-point evaluation after the actual finite cover. -/
@[reassoc] theorem universal_commutes :
    Q.universalToFamilySquare ≫ F.squareEvaluation =
      Q.universalToHomSource ≫ evaluation P H U := by
  apply pullback.hom_ext
  · simp only [Category.assoc, F.squareEvaluation_first,
      evaluation_first, universalToFamilySquare, pullback.lift_fst_assoc]
    exact Q.universalFirst_evaluation
  · simp only [Category.assoc, F.squareEvaluation_second,
      evaluation_second, universalToFamilySquare, pullback.lift_snd_assoc]
    exact Q.universalSecond_evaluation

include Q in
open LeBrunSalamon.Refinement.HomTwoPointEvaluation in
theorem squareEvaluation_dominant_of_hom
    (h : DenseRange (evaluation P H U).base) : DenseRange F.squareEvaluation.base := by
  change Dense (Set.range (evaluation P H U)) at h
  change Dense (Set.range F.squareEvaluation)
  apply h.mono
  rintro _ ⟨z, rfl⟩
  obtain ⟨w, hw⟩ := Q.universalToHomSource_surjective z
  refine ⟨Q.universalToFamilySquare w, ?_⟩
  have he := congrArg (fun k => k w) Q.universal_commutes
  simpa only [Scheme.Hom.comp_apply, hw] using he

end HomTwoPointEvaluationNames

include Q in
theorem squareEvaluation_dominant
    (hU : Smooth (U.ι ≫ H.toC))
    (t : PointsOver ComplexBase (𝟙 ComplexBase) U.toScheme (U.ι ≫ H.toC))
    (f : RationalCurve P X)
    (hf : f.map = H.mapAt P
      ⟨t.val ≫ U.ι, by simpa only [Category.assoc] using t.property⟩)
    (hfree : IsVeryFreeRationalCurve P X (intrinsicTangentBundle X) f) :
    DenseRange F.squareEvaluation.base :=
  Q.squareEvaluation_dominant_of_hom
    (LeBrunSalamon.StandardInputs.homOpen_twoPointEvaluation_dominant P X H U hU t f hf hfree)

variable (t : PointsOver ComplexBase (𝟙 ComplexBase) U.toScheme (U.ι ≫ H.toC))

def wholeSquareParameter : SelfProduct P.structureMap ⟶ U.toScheme :=
  firstProjection P.structureMap ≫ P.structureMap ≫ t.val

/-- Base change of the finite cover along the constant parameter map
from the entire source square. This construction includes every point
of the diagonal automatically. -/
abbrev MemberCover : Scheme := pullback Q.toHom (wholeSquareParameter t)

abbrev memberToSquare : Q.MemberCover t ⟶ SelfProduct P.structureMap :=
  pullback.snd Q.toHom (wholeSquareParameter t)

abbrev memberToCover : Q.MemberCover t ⟶ Q.cover :=
  pullback.fst Q.toHom (wholeSquareParameter t)

theorem memberToSquare_finite : IsFinite (Q.memberToSquare t) := by
  letI : IsFinite Q.toHom := Q.finite
  exact inferInstance

theorem memberToSquare_proper : IsProper (Q.memberToSquare t) := by
  letI : IsFinite (Q.memberToSquare t) := Q.memberToSquare_finite t
  exact inferInstance

theorem memberToSquare_surjective : Function.Surjective (Q.memberToSquare t) := by
  letI : Surjective Q.toHom := Q.surjective
  exact (Q.memberToSquare t).surjective

@[reassoc] theorem memberToCover_toHom :
    Q.memberToCover t ≫ Q.toHom =
      Q.memberToSquare t ≫ firstProjection P.structureMap ≫ P.structureMap ≫ t.val := by
  exact pullback.condition

theorem member_first_overC :
    (Q.memberToSquare t ≫ firstProjection P.structureMap) ≫ P.structureMap =
      Q.memberToCover t ≫ Q.coverToC := by
  simp only [coverToC, ← Category.assoc, Q.memberToCover_toHom t]
  simp only [Category.assoc, t.property, Category.comp_id]

theorem member_second_overC :
    (Q.memberToSquare t ≫ secondProjection P.structureMap) ≫ P.structureMap =
      Q.memberToCover t ≫ Q.coverToC := by
  rw [Category.assoc, ← pullback.condition]
  simpa only [Category.assoc] using Q.member_first_overC t

def memberFirst : Q.MemberCover t ⟶ F.source :=
  pullback.lift (Q.memberToSquare t ≫ firstProjection P.structureMap)
    (Q.memberToCover t) (Q.member_first_overC t) ≫ Q.sourceMap

def memberSecond : Q.MemberCover t ⟶ F.source :=
  pullback.lift (Q.memberToSquare t ≫ secondProjection P.structureMap)
    (Q.memberToCover t) (Q.member_second_overC t) ≫ Q.sourceMap

@[reassoc] theorem memberFirst_parameter :
    Q.memberFirst t ≫ F.parameter = Q.memberToCover t ≫ Q.coverToBase := by
  simp only [memberFirst, Category.assoc, Q.sourceMap_parameter,
    pullback.lift_snd_assoc]

@[reassoc] theorem memberSecond_parameter :
    Q.memberSecond t ≫ F.parameter = Q.memberToCover t ≫ Q.coverToBase := by
  simp only [memberSecond, Category.assoc, Q.sourceMap_parameter,
    pullback.lift_snd_assoc]

def memberToFamilySquare : Q.MemberCover t ⟶ F.Square :=
  pullback.lift (Q.memberFirst t) (Q.memberSecond t)
    ((Q.memberFirst_parameter t).trans (Q.memberSecond_parameter t).symm)

/-- The whole-member cover factors through the same parametrized
square used for descent of the smooth-family sections. -/
def memberToParametrizedSquare : Q.MemberCover t ⟶ Q.ParametrizedSquare :=
  pullback.lift
    (pullback.lift (Q.memberToSquare t ≫ firstProjection P.structureMap)
      (Q.memberToCover t) (Q.member_first_overC t))
    (pullback.lift (Q.memberToSquare t ≫ secondProjection P.structureMap)
      (Q.memberToCover t) (Q.member_second_overC t)) (by
        simp only [parametrizedParameter, pullback.lift_snd])

@[reassoc] theorem memberToParametrizedSquare_base :
    Q.memberToParametrizedSquare t ≫ Q.parametrizedSquareToCover =
      Q.memberToCover t := by
  simp only [memberToParametrizedSquare, parametrizedSquareToCover,
    parametrizedParameter, Category.assoc, pullback.lift_fst_assoc,
    pullback.lift_snd]

@[reassoc] theorem memberToParametrizedSquare_family :
    Q.memberToParametrizedSquare t ≫ Q.parametrizedSquareToFamily =
      Q.memberToFamilySquare t := by
  apply pullback.hom_ext
  · simp only [Category.assoc, Q.parametrizedSquareToFamily_first,
      memberToParametrizedSquare, pullback.lift_fst_assoc,
      memberToFamilySquare, pullback.lift_fst, memberFirst]
  · simp only [Category.assoc, Q.parametrizedSquareToFamily_second,
      memberToParametrizedSquare, pullback.lift_snd_assoc,
      memberToFamilySquare, pullback.lift_snd, memberSecond]

theorem sourceMap_atMember {T : Scheme} (z : T ⟶ ProjectiveLine) (q : T ⟶ Q.cover)
    (h : z ≫ P.structureMap = q ≫ Q.coverToC)
    (hq : q ≫ Q.toHom = z ≫ P.structureMap ≫ t.val) :
    pullback.lift z q h ≫ Q.sourceMap ≫ F.evaluation =
      z ≫ H.mapAt P
        ⟨t.val ≫ U.ι, by simpa only [Category.assoc] using t.property⟩ := by
  rw [Q.sourceMap_evaluation]
  dsimp only [HomSpacePresentation.mapAt]
  simp only [← Category.assoc]
  apply congrArg (fun k => k ≫ H.evaluation)
  apply pullback.hom_ext
  · simp only [rationalSourceMap, Category.assoc, pullback.lift_fst,
      pullback.lift_fst_assoc, Category.comp_id]
  · simp only [rationalSourceMap, Category.assoc, pullback.lift_snd,
      pullback.lift_snd_assoc]
    simpa only [Category.assoc] using congrArg (fun k => k ≫ U.ι) hq

@[reassoc] theorem memberFirst_evaluation :
    Q.memberFirst t ≫ F.evaluation =
      Q.memberToSquare t ≫ firstProjection P.structureMap ≫ H.mapAt P
        ⟨t.val ≫ U.ι, by simpa only [Category.assoc] using t.property⟩ := by
  simpa only [memberFirst, Category.assoc] using
    Q.sourceMap_atMember t (Q.memberToSquare t ≫ firstProjection P.structureMap)
      (Q.memberToCover t) (Q.member_first_overC t)
      (by simpa only [Category.assoc] using Q.memberToCover_toHom t)

@[reassoc] theorem memberSecond_evaluation :
    Q.memberSecond t ≫ F.evaluation =
      Q.memberToSquare t ≫ secondProjection P.structureMap ≫ H.mapAt P
        ⟨t.val ≫ U.ι, by simpa only [Category.assoc] using t.property⟩ := by
  have hq : Q.memberToCover t ≫ Q.toHom =
      (Q.memberToSquare t ≫ secondProjection P.structureMap) ≫
        P.structureMap ≫ t.val := by
    calc
      _ = Q.memberToSquare t ≫ firstProjection P.structureMap ≫
          P.structureMap ≫ t.val := Q.memberToCover_toHom t
      _ = _ := by
        simpa only [Category.assoc] using congrArg
          (fun k => Q.memberToSquare t ≫ k ≫ t.val)
          (pullback.condition (f := P.structureMap) (g := P.structureMap))
  simpa only [memberSecond, Category.assoc] using
    Q.sourceMap_atMember t (Q.memberToSquare t ≫ secondProjection P.structureMap)
      (Q.memberToCover t) (Q.member_second_overC t) hq

/-- Exact commutativity for the whole-square cover of an arbitrary
member, including coincident points. The map is the original mapAt,
not merely another map with the same point labels. -/
@[reassoc] theorem member_commutes (f : RationalCurve P X)
    (hf : f.map = H.mapAt P
      ⟨t.val ≫ U.ι, by simpa only [Category.assoc] using t.property⟩) :
    Q.memberToFamilySquare t ≫ F.squareEvaluation =
      Q.memberToSquare t ≫ LeBrunSalamon.Refinement.curveSquareMap P f := by
  apply pullback.hom_ext
  · simp only [Category.assoc, F.squareEvaluation_first,
      LeBrunSalamon.Refinement.curveSquareMap_first, memberToFamilySquare,
      pullback.lift_fst_assoc]
    simpa only [Category.assoc, hf] using Q.memberFirst_evaluation t
  · simp only [Category.assoc, F.squareEvaluation_second,
      LeBrunSalamon.Refinement.curveSquareMap_second, memberToFamilySquare,
      pullback.lift_snd_assoc]
    simpa only [Category.assoc, hf] using Q.memberSecond_evaluation t

end FullHomComparison

namespace FormalArcs

/- Trait and toC are imported from LSProjectivityDefinitions. -/

def closedPoint : ComplexBase ⟶ Trait :=
  Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff : PowerSeries ℂ →+* ℂ))

@[reassoc] theorem closedPoint_toC : closedPoint ≫ toC = 𝟙 ComplexBase := by
  rw [closedPoint, toC, ← Spec.map_comp]
  have h : (CommRingCat.ofHom (PowerSeries.C : ℂ →+* PowerSeries ℂ)) ≫
      CommRingCat.ofHom (PowerSeries.constantCoeff : PowerSeries ℂ →+* ℂ) =
        𝟙 (CommRingCat.of ℂ) := by
    ext c
    exact PowerSeries.constantCoeff_C c
  rw [h, Spec.map_id]

/-- Regularity of the pullback of the supplied rational section along
the supplied actual formal arc. The equality uses the adjunction-unit
pullback on the full inverse-image open. No target trivialization or
pointwise surrogate appears in this condition. -/
def Regular {Y : Scheme} {E : OModule Y}
    (s : NormalExtension.RationalSection E) (gamma : Trait ⟶ Y) : Prop :=
  ∃ w : GlobalSections (pullbackModule gamma E),
    (pullbackModule gamma E).presheaf.map
      (homOfLE (le_top : gamma ⁻¹ᵁ s.domain ≤ ⊤)).op w =
        pullLocalSection gamma E s.domain s.value

end FormalArcs

end LeBrunSalamon.Construction.StableMaps

namespace LeBrunSalamon.StandardInputs

/-- Scheme-level stable-map compactification, combining Behrend--Manin
(Duke Math. J. 85 (1996), Theorem 3.14, Proposition 4.1 and Corollaries
4.6/4.8) with Edidin--Hassett--Kresch--Vistoli (Amer. J. Math. 123
(2001), Theorem 2.7). Normalize a component dominating the normalized
stable-map component; the actual universal curve pulls back to a scheme.

The supplied `FreeOpen` is affine, irreducible and smooth. Its entire
base change gives the finite cover and the normalized source/evaluation
comparison. Actual component gluing uses Stacks 0C4J and the split-node
description 0C46; actual P1 components use 0C6U. This is a composite
classical corollary, with no contact or vector-extension conclusion.
Exact header independently reviewed by root and calculus. -/
theorem stableMapSchemeCover_exists
    (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {d : ℕ} (X : SmoothProperComplexVariety d) (hX : HasProjectiveEmbedding X)
    (H : HomSpacePresentation P X) (f : RationalCurve P X)
    (hf : IsFreeRationalCurve P X (intrinsicTangentBundle X) f)
    (L : LineBundle X.scheme) (hL : IsAmpleLine L)
    (O : LeBrunSalamon.Construction.HomNeighborhood.FreeOpen P p X H f L)
    (degree : ℕ) (positive : 0 < degree)
    (hdegree : degreeOnCurve P p f.toParametrizedCurve L = (degree : ℤ)) :
    Nonempty (Σ F : LeBrunSalamon.Construction.StableMaps.ProjectiveNodalFamily
        P p X L degree,
      LeBrunSalamon.Construction.StableMaps.FullHomComparison
        P p X H O.neighborhood L degree F) := by
  sorry


/-- General normality of the actual square of a generically smooth
geometrically integral nodal curve family; there is no degree, stable-map,
target, contact or section hypothesis or conclusion. -/
theorem nodalCurveSquare_normal
    {B C : Scheme} [IsIntegral B] [IsLocallyNoetherian B]
    (hB : LeBrunSalamon.Construction.Descent.NormalScheme B)
    (pi : C ⟶ B) [Flat pi] [LocallyOfFinitePresentation pi]
    (hnode : LeBrunSalamon.Construction.StableMaps.IsNodalCurve pi)
    (V : B.Opens) (hV : Dense (V : Set B))
    [Smooth (pullback.snd pi V.ι)]
    [GeometricallyIntegral (pullback.snd pi V.ι)] :
    IsIntegral (pullback pi pi) ∧
      LeBrunSalamon.Construction.Descent.NormalScheme (pullback pi pi) := by
  sorry

/-- General formal-arc detection of divisorial poles for a locally free
sheaf on a normal integral finite-type complex scheme. All actual C[[t]]
arcs with generic point in the given domain are tested, not just arcs in
the base of a family. This does not identify a height-one residue field
with C. The output is the ordinary geometric regularity predicate at
every height-one point, to be used with the existing normal extension
theorem. -/
theorem heightOne_regular_of_formalArcs
    {Y : Scheme} [IsIntegral Y]
    (sY : Y ⟶ ComplexBase) [LocallyOfFiniteType sY]
    (hY : LeBrunSalamon.Construction.Descent.NormalScheme Y)
    {r : ℕ} (E : AlgebraicVectorBundle Y r)
    (s : LeBrunSalamon.Construction.NormalExtension.RationalSection E.sheaf)
    (htest : ∀ gamma :
      PointsOver LeBrunSalamon.Construction.StableMaps.FormalArcs.Trait
        LeBrunSalamon.Construction.StableMaps.FormalArcs.toC Y sY,
      Dense (gamma.val ⁻¹ᵁ s.domain :
        Set LeBrunSalamon.Construction.StableMaps.FormalArcs.Trait) →
      LeBrunSalamon.Construction.StableMaps.FormalArcs.Regular s gamma.val) :
    ∀ y : Y, ringKrullDim (Y.presheaf.stalk y) = 1 →
      LeBrunSalamon.Construction.NormalExtension.RegularAt s y := by
  sorry

end LeBrunSalamon.StandardInputs

namespace LeBrunSalamon.Construction.StableMaps.ProjectiveNodalFamily

variable {P : ProjectiveLineOverC} {p : ProjectiveLinePoint P}
variable {d : ℕ} {X : SmoothProperComplexVariety d}
variable {L : LineBundle X.scheme} {degree : ℕ}
variable (F : ProjectiveNodalFamily P p X L degree)

theorem square_integral_and_normal :
    IsIntegral F.Square ∧ Descent.NormalScheme F.Square := by
  letI : IsIntegral F.base := F.baseIntegral
  letI : IsLocallyNoetherian F.base := F.base_locallyNoetherian
  letI : Flat F.parameter := F.flat
  letI : LocallyOfFinitePresentation F.parameter := F.finitePresentation
  letI : SmoothOfRelativeDimension 1 (pullback.snd F.parameter F.smoothOpen.ι) := F.smooth
  letI : Smooth (pullback.snd F.parameter F.smoothOpen.ι) :=
    SmoothOfRelativeDimension.smooth (n := 1) _
  letI : GeometricallyIntegral (pullback.snd F.parameter F.smoothOpen.ι) :=
    F.smoothGeometricallyIntegral
  exact LeBrunSalamon.StandardInputs.nodalCurveSquare_normal
    F.baseNormal F.parameter F.nodal F.smoothOpen F.smoothDense

theorem square_integral : IsIntegral F.Square := F.square_integral_and_normal.1

theorem square_normal : Descent.NormalScheme F.Square := F.square_integral_and_normal.2

theorem square_integralScheme : Descent.IntegralScheme F.Square := by
  letI : IsIntegral F.Square := F.square_integral
  exact ⟨inferInstance, fun _ => inferInstance⟩

theorem smoothSquareOpen_dense : Dense (F.smoothSquareOpen : Set F.Square) := by
  letI : Flat F.parameter := F.flat
  letI : LocallyOfFinitePresentation F.parameter := F.finitePresentation
  letI : Flat F.squareToBase := by
    change Flat (pullback.fst F.parameter F.parameter ≫ F.parameter)
    infer_instance
  letI : LocallyOfFinitePresentation F.squareToBase := by
    change LocallyOfFinitePresentation (pullback.fst F.parameter F.parameter ≫ F.parameter)
    infer_instance
  exact F.smoothDense.preimage F.squareToBase.isOpenMap

/-- Regularity on all actual total-space arcs gives exactly the
height-one hypotheses used by the existing extension theorem. -/
theorem regularAt_heightOne_of_arcs {r : ℕ} (E : AlgebraicVectorBundle F.Square r)
    (s : NormalExtension.RationalSection E.sheaf)
    (htest : ∀ gamma : PointsOver FormalArcs.Trait FormalArcs.toC F.Square
      (F.squareToBase ≫ F.toC),
      Dense (gamma.val ⁻¹ᵁ s.domain : Set FormalArcs.Trait) →
        FormalArcs.Regular s gamma.val) :
    ∀ y : F.Square, ringKrullDim (F.Square.presheaf.stalk y) = 1 →
      NormalExtension.RegularAt s y := by
  letI : IsIntegral F.Square := F.square_integral
  letI : IsProper F.squareToBase := F.squareToBase_proper
  letI : IsProper F.toC := F.baseProper
  exact LeBrunSalamon.StandardInputs.heightOne_regular_of_formalArcs
    (F.squareToBase ≫ F.toC) F.square_normal E s htest

end LeBrunSalamon.Construction.StableMaps.ProjectiveNodalFamily

namespace LeBrunSalamon.Construction.StableMaps

open LeBrunSalamon.Core LeBrunSalamon.PhaseThirtyFive in
/-- Assemble the previously constructed full Hom neighbourhood with its
actual stable-map family and the finite comparison over every member.
Only the generic stable-map existence input is used here. -/
theorem conicFamily_exists (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    {n : ℕ} (X : ContactFanoManifold n) (g : VeryFreeContactConic P p X) :
    Nonempty (Σ N : FullConicNeighborhood P p X g,
      Σ F : ProjectiveNodalFamily P p X.variety X.contact.sequence.line 2,
        FullHomComparison P p X.variety N.homSpace N.neighborhood
          X.contact.sequence.line 2 F) := by
  classical
  obtain ⟨H⟩ := homSpacePresentation_exists P X.variety
    (contactFano_hasProjectiveEmbedding X)
  obtain ⟨O⟩ := HomNeighborhood.StandardInputs.free_neighborhood P p X.variety
    (contactFano_hasProjectiveEmbedding X) H g.curve
    (HomNeighborhood.veryFree_isFree P X.variety g.curve g.veryFree)
    X.contact.sequence.line
  obtain ⟨⟨F, Q⟩⟩ := LeBrunSalamon.StandardInputs.stableMapSchemeCover_exists P p
    X.variety (contactFano_hasProjectiveEmbedding X) H g.curve
    (HomNeighborhood.veryFree_isFree P X.variety g.curve g.veryFree)
    X.contact.sequence.line (contactFano_contactLine_ample X) O 2 (by decide)
    g.contactDegreeTwo
  let N : FullConicNeighborhood P p X g := {
    homSpace := H
    neighborhood := O.neighborhood
    marked := O.marked
    center := O.center
    smooth := O.smooth
    curveAt := O.curveAt
    curveAt_spec := O.curveAt_spec
    degreeTwo := fun t => (O.degree t).trans g.contactDegreeTwo
    veryFree := O.preservesVeryFree g.veryFree }
  exact ⟨⟨N, F, Q⟩⟩

end LeBrunSalamon.Construction.StableMaps

end
