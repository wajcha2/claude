import LSConicJets
import LSNodalFixedEnds
import LSStableMapFamily
import LSMovingPairAssembly
import LSRelativeDifferential
import LSFamilyDerivativeRestriction

/-!
# The two tensor sections on an actual parametrized family

The differential is taken relative to the parameter scheme. The source
tensor is pulled from the original normalized tensor on P1 x P1. All
external-product comparisons below are the canonical pullback maps.
These constructions are valid over arbitrary parameter schemes; their
descent will use equality on the actual overlap of parametrizations.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Core LeBrunSalamon.Skeleton LeBrunSalamon.Refinement

namespace LeBrunSalamon.Construction.FamilyBivectors

open ContactDerivativeIsoProof

-- Expose the same existing type aliases used by the checked conic chain rule.
set_option allowUnsafeReducibility true
attribute [local reducible] projectiveLineVariety identityCurveContact intrinsicTangentBundle

/-- Naturality of the actual equality comparison on pullbacks. -/
theorem pullbackEquality_naturality {Y X : Scheme} {f g : Y ⟶ X}
    (h : f = g) {E E' : OModule X} (a : E ⟶ E') :
    (Scheme.Modules.pullback f).map a ≫
        eqToHom (congrArg (fun q => pullbackModule q E') h) =
      eqToHom (congrArg (fun q => pullbackModule q E) h) ≫
        (Scheme.Modules.pullback g).map a := by
  subst g
  simp

@[reassoc] theorem pullbackSquare_naturality {T Y W Z : Scheme}
    (a : T ⟶ Y) (b : Y ⟶ Z) (c : T ⟶ W) (d : W ⟶ Z)
    (h : a ≫ b = c ≫ d) {E E' : OModule Z} (v : E ⟶ E') :
    (Scheme.Modules.pullback a).map ((Scheme.Modules.pullback b).map v) ≫
        (pullbackSquareIso a b c d h E').hom =
      (pullbackSquareIso a b c d h E).hom ≫
        (Scheme.Modules.pullback c).map ((Scheme.Modules.pullback d).map v) := by
  have hab := (Scheme.Modules.pullbackComp a b).hom.naturality v
  change (Scheme.Modules.pullback a).map ((Scheme.Modules.pullback b).map v) ≫
      (Scheme.Modules.pullbackComp a b).hom.app E' =
    (Scheme.Modules.pullbackComp a b).hom.app E ≫
      (Scheme.Modules.pullback (a ≫ b)).map v at hab
  have hcd := (Scheme.Modules.pullbackComp c d).inv.naturality v
  change (Scheme.Modules.pullback (c ≫ d)).map v ≫
      (Scheme.Modules.pullbackComp c d).inv.app E' =
    (Scheme.Modules.pullbackComp c d).inv.app E ≫
      (Scheme.Modules.pullback c).map ((Scheme.Modules.pullback d).map v) at hcd
  have h₁ := congrArg (fun u :
      pullbackModule a (pullbackModule b E) ⟶ pullbackModule (a ≫ b) E' =>
    u ≫ eqToHom (congrArg (fun q => pullbackModule q E') h) ≫
      (Scheme.Modules.pullbackComp c d).inv.app E') hab
  have h₂ := congrArg (fun u : pullbackModule (a ≫ b) E ⟶ pullbackModule (c ≫ d) E' =>
    (Scheme.Modules.pullbackComp a b).hom.app E ≫ u ≫
      (Scheme.Modules.pullbackComp c d).inv.app E')
    (pullbackEquality_naturality h v)
  have h₃ := congrArg (fun u :
      pullbackModule (c ≫ d) E ⟶ pullbackModule c (pullbackModule d E') =>
    (Scheme.Modules.pullbackComp a b).hom.app E ≫
      eqToHom (congrArg (fun q => pullbackModule q E) h) ≫ u) hcd
  simp only [Category.assoc] at h₁ h₂ h₃
  simp only [pullbackSquareIso, Iso.trans_hom, Iso.symm_hom,
    eqToIso.hom, Iso.app_hom, Iso.app_inv, Category.assoc]
  exact h₁.trans (h₂.trans h₃)

@[reassoc] theorem tensorPullback_naturality {Y Z : Scheme} (f : Y ⟶ Z)
    {E E' F F' : OModule Z} (a : E ⟶ E') (b : F ⟶ F') :
    tensorMap ((Scheme.Modules.pullback f).map a) ((Scheme.Modules.pullback f).map b) ≫
        tensorPullbackComparison f E' F' =
      tensorPullbackComparison f E F ≫ (Scheme.Modules.pullback f).map (tensorMap a b) := by
  exact ExternalExchangeCoherenceProof.comparison_naturality f a b

namespace RelativeSquare

variable {C B : Scheme} (pi : C ⟶ B)

abbrev Space := pullback pi pi
abbrev left : Space pi ⟶ C := pullback.fst pi pi
abbrev right : Space pi ⟶ C := pullback.snd pi pi

def box (E F : OModule C) : OModule (Space pi) :=
  tensorSheaf (pullbackModule (left pi) E) (pullbackModule (right pi) F)

def boxMap {E E' F F' : OModule C} (a : E ⟶ E') (b : F ⟶ F') :
    box pi E F ⟶ box pi E' F' :=
  tensorMap ((Scheme.Modules.pullback (left pi)).map a)
    ((Scheme.Modules.pullback (right pi)).map b)

@[reassoc] theorem boxMap_comp {E E' E'' F F' F'' : OModule C}
    (a : E ⟶ E') (a' : E' ⟶ E'') (b : F ⟶ F') (b' : F' ⟶ F'') :
    boxMap pi a b ≫ boxMap pi a' b' = boxMap pi (a ≫ a') (b ≫ b') := by
  simp only [boxMap, Functor.map_comp, tensorMap_comp]

def evaluation {X : Scheme} (sX : X ⟶ ComplexBase) (sB : B ⟶ ComplexBase)
    (e : C ⟶ X) (he : e ≫ sX = pi ≫ sB) :
    Space pi ⟶ SelfProduct sX :=
  pullback.lift (left pi ≫ e) (right pi ≫ e) (by
    simp only [Category.assoc, he]
    simpa only [Category.assoc] using congrArg (fun q => q ≫ sB)
      (pullback.condition (f := pi) (g := pi)))

@[reassoc] theorem evaluation_left {X : Scheme} (sX : X ⟶ ComplexBase)
    (sB : B ⟶ ComplexBase) (e : C ⟶ X) (he : e ≫ sX = pi ≫ sB) :
    evaluation pi sX sB e he ≫ firstProjection sX = left pi ≫ e :=
  pullback.lift_fst _ _ _

@[reassoc] theorem evaluation_right {X : Scheme} (sX : X ⟶ ComplexBase)
    (sB : B ⟶ ComplexBase) (e : C ⟶ X) (he : e ≫ sX = pi ≫ sB) :
    evaluation pi sX sB e he ≫ secondProjection sX = right pi ≫ e :=
  pullback.lift_snd _ _ _

/-- External products on the source and target are identified through
the two literal commuting projection squares. -/
def comparison {X : Scheme} (sX : X ⟶ ComplexBase) (sB : B ⟶ ComplexBase)
    (e : C ⟶ X) (he : e ≫ sX = pi ≫ sB) (E F : OModule X) :
    box pi (pullbackModule e E) (pullbackModule e F) ⟶
      pullbackModule (evaluation pi sX sB e he) (externalTensor sX E F) :=
  tensorMap
    (pullbackSquareIso (left pi) e (evaluation pi sX sB e he)
      (firstProjection sX) (evaluation_left pi sX sB e he).symm E).hom
    (pullbackSquareIso (right pi) e (evaluation pi sX sB e he)
      (secondProjection sX) (evaluation_right pi sX sB e he).symm F).hom ≫
    tensorPullbackComparison (evaluation pi sX sB e he)
      (pullbackModule (firstProjection sX) E) (pullbackModule (secondProjection sX) F)

theorem comparison_isIso {X : Scheme} (sX : X ⟶ ComplexBase)
    (sB : B ⟶ ComplexBase) (e : C ⟶ X) (he : e ≫ sX = pi ≫ sB)
    (E F : OModule X) : IsIso (comparison pi sX sB e he E F) := by
  let l := pullbackSquareIso (left pi) e (evaluation pi sX sB e he)
    (firstProjection sX) (evaluation_left pi sX sB e he).symm E
  let r := pullbackSquareIso (right pi) e (evaluation pi sX sB e he)
    (secondProjection sX) (evaluation_right pi sX sB e he).symm F
  letI := tensorPullbackComparison_isIso (evaluation pi sX sB e he)
    (pullbackModule (firstProjection sX) E) (pullbackModule (secondProjection sX) F)
  change IsIso ((tensorIso l r).hom ≫ _)
  infer_instance

@[reassoc] theorem comparison_naturality {X : Scheme} (sX : X ⟶ ComplexBase)
    (sB : B ⟶ ComplexBase) (e : C ⟶ X) (he : e ≫ sX = pi ≫ sB)
    {E E' F F' : OModule X} (a : E ⟶ E') (b : F ⟶ F') :
    boxMap pi ((Scheme.Modules.pullback e).map a) ((Scheme.Modules.pullback e).map b) ≫
        comparison pi sX sB e he E' F' =
      comparison pi sX sB e he E F ≫
        (Scheme.Modules.pullback (evaluation pi sX sB e he)).map
          (externalTensorMap sX a b) := by
  unfold comparison boxMap externalTensorMap
  rw [← Category.assoc, ← tensorMap_comp]
  rw [pullbackSquare_naturality, pullbackSquare_naturality]
  rw [tensorMap_comp, Category.assoc, tensorPullback_naturality]
  simp only [Category.assoc]

end RelativeSquare

namespace Parametrized

variable (P : ProjectiveLineOverC) {B : Scheme} (sB : B ⟶ ComplexBase)

abbrev Source := RationalSourceOver P B sB
abbrev projection : Source P sB ⟶ ProjectiveLine := pullback.fst P.structureMap sB
abbrev parameter : Source P sB ⟶ B := pullback.snd P.structureMap sB
abbrev Square := RelativeSquare.Space (parameter P sB)

def sourceSquare : Square P sB ⟶ SelfProduct P.structureMap :=
  RelativeSquare.evaluation (parameter P sB) P.structureMap sB (projection P sB)
    (pullback.condition (f := P.structureMap) (g := sB))

def sourceComparison :
    RelativeSquare.box (parameter P sB)
      (pullbackModule (projection P sB) (tangentSheaf P.structureMap))
      (pullbackModule (projection P sB) (tangentSheaf P.structureMap)) ⟶
      pullbackModule (sourceSquare P sB)
        (externalTensor P.structureMap (tangentSheaf P.structureMap)
          (tangentSheaf P.structureMap)) :=
  RelativeSquare.comparison (parameter P sB) P.structureMap sB (projection P sB)
    (pullback.condition (f := P.structureMap) (g := sB))
    (tangentSheaf P.structureMap) (tangentSheaf P.structureMap)

theorem sourceComparison_isIso : IsIso (sourceComparison P sB) :=
  RelativeSquare.comparison_isIso (parameter P sB) P.structureMap sB
    (projection P sB) (pullback.condition (f := P.structureMap) (g := sB)) _ _

/-- The original normalized source bivector on the whole relative
square. In particular, the diagonal is retained. -/
def bivector : AlgebraicSection
    (RelativeSquare.box (parameter P sB)
      (pullbackModule (projection P sB) (tangentSheaf P.structureMap))
      (pullbackModule (projection P sB) (tangentSheaf P.structureMap))) := by
  letI := sourceComparison_isIso P sB
  exact pullSection (sourceSquare P sB) (sourceBivector P) ≫ inv (sourceComparison P sB)

@[reassoc] theorem bivector_comparison :
    bivector P sB ≫ sourceComparison P sB =
      pullSection (sourceSquare P sB) (sourceBivector P) := by
  letI := sourceComparison_isIso P sB
  simp only [bivector, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

variable {d : ℕ} (X : SmoothProperComplexVariety d)
variable (e : Source P sB ⟶ X.scheme)
variable (he : e ≫ X.structureMap = parameter P sB ≫ sB)

def relativeCotangentMap : pullbackModule e (cotangentSheaf X.structureMap) ⟶
    cotangentSheaf (parameter P sB) :=
  cotangentMap e X.structureMap ≫ eqToHom (congrArg cotangentSheaf he) ≫
    cotangentToRelative (parameter P sB) sB

theorem relativeCotangentMap_differential (U : X.scheme.Opens)
    (a : RingSections X.scheme U) :
    (relativeCotangentMap P sB X e he).app (e ⁻¹ᵁ U)
      (pullLocalSection e (cotangentSheaf X.structureMap) U
        ((cotangentPresentation X.structureMap).differential.apply U a)) =
      (cotangentPresentation (parameter P sB)).differential.apply
        (e ⁻¹ᵁ U) (e.app U a) := by
  change (cotangentToRelative (parameter P sB) sB).app _
    ((eqToHom (congrArg cotangentSheaf he)).app _
      ((cotangentMap e X.structureMap).app _
        (pullLocalSection e (cotangentSheaf X.structureMap) U
          ((cotangentPresentation X.structureMap).differential.apply U a)))) = _
  rw [ContactDerivativeIsoProof.cotangentMap_differential,
    ContactDerivativeIsoProof.differential_transport _ _ he,
    CotangentTransitivityRederivedV02.cotangentToRelative_differential]

def relativeCotangent : pullbackModule e (cotangentSheaf X.structureMap) ⟶
    pullbackModule (projection P sB) (cotangentSheaf P.structureMap) := by
  letI := LeBrunSalamon.StandardInputs.cotangentPullback_isIso P.structureMap sB
  exact relativeCotangentMap P sB X e he ≫
    inv (CotangentBaseChange.canonicalMap P.structureMap sB)

def differential : pullbackModule (projection P sB) (tangentSheaf P.structureMap) ⟶
    pullbackModule e (tangentSheaf X.structureMap) := by
  letI := dualBaseChange_isIso e (smooth_cotangent_rank X.structureMap d X.smooth)
  exact dualBaseChange (projection P sB) (cotangentSheaf P.structureMap) ≫
    dualMap (relativeCotangent P sB X e he) ≫
      inv (dualBaseChange e (cotangentSheaf X.structureMap))

@[reassoc] theorem differential_normalized :
    differential P sB X e he ≫ dualBaseChange e (cotangentSheaf X.structureMap) =
      dualBaseChange (projection P sB) (cotangentSheaf P.structureMap) ≫
        dualMap (relativeCotangent P sB X e he) := by
  letI := dualBaseChange_isIso e (smooth_cotangent_rank X.structureMap d X.smooth)
  simp only [differential, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

def evaluationSquare : Square P sB ⟶ SelfProduct X.structureMap :=
  RelativeSquare.evaluation (parameter P sB) X.structureMap sB e he

/-- Restriction to an entire complex fibre, before any point evaluation.
The parameter is fixed and the source coordinate is the identity. -/
theorem relativeCotangent_atSection
    (b : ComplexBase ⟶ B) (hb : b ≫ sB = 𝟙 ComplexBase)
    (j : ProjectiveLine ⟶ Source P sB)
    (hj₁ : j ≫ projection P sB = 𝟙 ProjectiveLine)
    (hj₂ : j ≫ parameter P sB = P.structureMap ≫ b)
    (hf : (j ≫ e) ≫ X.structureMap = P.structureMap) :
    (Scheme.Modules.pullback j).map (relativeCotangent P sB X e he) ≫
        (RelativeDifferential.sectionPullbackIso j (projection P sB) hj₁
          (cotangentSheaf P.structureMap)).hom =
      (Scheme.Modules.pullbackComp j e).hom.app (cotangentSheaf X.structureMap) ≫
        ContactDerivativeIsoProof.cotangentOver (projectiveLineVariety P) X (j ≫ e) hf := by
  letI := LeBrunSalamon.StandardInputs.cotangentPullback_isIso P.structureMap sB
  have hs := RelativeDifferential.section_baseChange P.structureMap sB b hb j hj₁ hj₂
  have hc : (j ≫ e) ≫ X.structureMap = P.structureMap ≫ (b ≫ sB) := by
    rw [hb, Category.comp_id]
    exact hf
  change (Scheme.Modules.pullback j).map (relativeCotangent P sB X e he) ≫
      (compositionPullback j (projection P sB) (𝟙 ProjectiveLine) hj₁
        (cotangentSheaf P.structureMap)).hom ≫
        (Scheme.Modules.pullbackId ProjectiveLine).hom.app (cotangentSheaf P.structureMap) = _
  rw [← hs]
  simp only [relativeCotangent, Functor.map_comp, Functor.map_inv,
    Category.assoc, IsIso.inv_hom_id_assoc]
  change (Scheme.Modules.pullback j).map
      (RelativeDifferential.cotangent (parameter P sB) X.structureMap e sB he) ≫
      RelativeDifferential.cotangent P.structureMap (parameter P sB) j b hj₂ = _
  rw [← RelativeDifferential.cotangent_comp P.structureMap
    (parameter P sB) X.structureMap j b e sB hj₂ he hc]
  rw [RelativeDifferential.cotangent_congr P.structureMap X.structureMap
    rfl hb hc (by simpa only [Category.comp_id] using hf)]
  simp only [eqToHom_refl, Category.id_comp]
  exact congrArg (fun k : pullbackModule (j ≫ e) (cotangentSheaf X.structureMap) ⟶
      cotangentSheaf P.structureMap =>
    (Scheme.Modules.pullbackComp j e).hom.app (cotangentSheaf X.structureMap) ≫ k)
    (RelativeDifferential.cotangent_overC (projectiveLineVariety P) X (j ≫ e) hf
      (by
        change (j ≫ e) ≫ X.structureMap = P.structureMap ≫ 𝟙 ComplexBase
        exact hf.trans (Category.comp_id P.structureMap).symm))

/-- The actual relative derivative specializes to the original derivative
of the entire fibre map. Both source and target pullbacks use the fixed
composition isomorphisms. -/
theorem differential_atSection
    (b : ComplexBase ⟶ B) (hb : b ≫ sB = 𝟙 ComplexBase)
    (j : ProjectiveLine ⟶ Source P sB)
    (hj₁ : j ≫ projection P sB = 𝟙 ProjectiveLine)
    (hj₂ : j ≫ parameter P sB = P.structureMap ≫ b)
    (hf : (j ≫ e) ≫ X.structureMap = P.structureMap) :
    (RelativeDifferential.sectionPullbackIso j (projection P sB) hj₁
        (tangentSheaf P.structureMap)).inv ≫
      (Scheme.Modules.pullback j).map (differential P sB X e he) ≫
        (Scheme.Modules.pullbackComp j e).hom.app (tangentSheaf X.structureMap) =
      differentialOver (projectiveLineVariety P) X (j ≫ e) hf := by
  letI := dualBaseChange_isIso e
    (smooth_cotangent_rank X.structureMap d X.smooth)
  letI := dualBaseChange_isIso (j ≫ e)
    (smooth_cotangent_rank X.structureMap d X.smooth)
  rw [ContactDerivativeIsoProof.differentialOver_dual]
  exact FamilyDerivativeRestriction.section_morphism
    j (projection P sB) e hj₁
    (cotangentSheaf P.structureMap) (cotangentSheaf X.structureMap)
    (relativeCotangent P sB X e he)
    (ContactDerivativeIsoProof.cotangentOver (projectiveLineVariety P) X (j ≫ e) hf)
    (relativeCotangent_atSection P sB X e he b hb j hj₁ hj₂ hf)

end Parametrized

namespace ParametrizedContact

variable (P : ProjectiveLineOverC) {B : Scheme} (sB : B ⟶ ComplexBase)
variable {n : ℕ} (X : ContactFanoManifold n)
variable (e : Parametrized.Source P sB ⟶ X.variety.scheme)
variable (he : e ≫ X.variety.structureMap = Parametrized.parameter P sB ≫ sB)

def velocity :
    pullbackModule (Parametrized.projection P sB) (tangentSheaf P.structureMap) ⟶
      pullbackModule e X.contact.sequence.line.sheaf :=
  Parametrized.differential P sB X.variety e he ≫
    (Scheme.Modules.pullback e).map X.contact.sequence.form

abbrev evaluationSquare := Parametrized.evaluationSquare P sB X.variety e he

/-- The first tensor uses the actual relative derivative in its first
factor and the actual contact derivative in its second. -/
def leftSection : AlgebraicSection
    (pullbackModule (evaluationSquare P sB X e he)
      (movingPairBundleLeft X.variety X.contact)) :=
  Parametrized.bivector P sB ≫
    RelativeSquare.boxMap (Parametrized.parameter P sB)
      (Parametrized.differential P sB X.variety e he) (velocity P sB X e he) ≫
    RelativeSquare.comparison (Parametrized.parameter P sB)
      X.variety.structureMap sB e he (tangentSheaf X.variety.structureMap)
        X.contact.sequence.line.sheaf

/-- The second tensor retains the relative derivative in its second
factor. Both sections live on the whole parametrized square. -/
def rightSection : AlgebraicSection
    (pullbackModule (evaluationSquare P sB X e he)
      (movingPairBundleRight X.variety X.contact)) :=
  Parametrized.bivector P sB ≫
    RelativeSquare.boxMap (Parametrized.parameter P sB)
      (velocity P sB X e he) (Parametrized.differential P sB X.variety e he) ≫
    RelativeSquare.comparison (Parametrized.parameter P sB)
      X.variety.structureMap sB e he X.contact.sequence.line.sheaf
        (tangentSheaf X.variety.structureMap)

def value : AlgebraicSection
    (pullbackModule (evaluationSquare P sB X e he)
      (externalSquareLine X.variety.structureMap X.contact.sequence.line).sheaf) :=
  Parametrized.bivector P sB ≫
    RelativeSquare.boxMap (Parametrized.parameter P sB)
      (velocity P sB X e he) (velocity P sB X e he) ≫
    RelativeSquare.comparison (Parametrized.parameter P sB)
      X.variety.structureMap sB e he
        X.contact.sequence.line.sheaf X.contact.sequence.line.sheaf

@[reassoc] theorem leftSection_contact :
    leftSection P sB X e he ≫
        (Scheme.Modules.pullback (evaluationSquare P sB X e he)).map
          (movingPairContactLeft X.variety X.contact) = value P sB X e he := by
  change (Parametrized.bivector P sB ≫
    RelativeSquare.boxMap (Parametrized.parameter P sB)
      (Parametrized.differential P sB X.variety e he) (velocity P sB X e he) ≫
    RelativeSquare.comparison (Parametrized.parameter P sB)
      X.variety.structureMap sB e he (tangentSheaf X.variety.structureMap)
        X.contact.sequence.line.sheaf) ≫
      (Scheme.Modules.pullback (evaluationSquare P sB X e he)).map
        (externalTensorMap X.variety.structureMap X.contact.sequence.form (𝟙 _)) = _
  simp only [Category.assoc]
  erw [← RelativeSquare.comparison_naturality (Parametrized.parameter P sB)
    X.variety.structureMap sB e he X.contact.sequence.form (𝟙 X.contact.sequence.line.sheaf)]
  rw [RelativeSquare.boxMap_comp_assoc]
  simp only [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

@[reassoc] theorem rightSection_contact :
    rightSection P sB X e he ≫
        (Scheme.Modules.pullback (evaluationSquare P sB X e he)).map
          (movingPairContactRight X.variety X.contact) = value P sB X e he := by
  change (Parametrized.bivector P sB ≫
    RelativeSquare.boxMap (Parametrized.parameter P sB)
      (velocity P sB X e he) (Parametrized.differential P sB X.variety e he) ≫
    RelativeSquare.comparison (Parametrized.parameter P sB)
      X.variety.structureMap sB e he X.contact.sequence.line.sheaf
        (tangentSheaf X.variety.structureMap)) ≫
      (Scheme.Modules.pullback (evaluationSquare P sB X e he)).map
        (externalTensorMap X.variety.structureMap (𝟙 _) X.contact.sequence.form) = _
  simp only [Category.assoc]
  erw [← RelativeSquare.comparison_naturality (Parametrized.parameter P sB)
    X.variety.structureMap sB e he (𝟙 X.contact.sequence.line.sheaf) X.contact.sequence.form]
  rw [RelativeSquare.boxMap_comp_assoc]
  simp only [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

theorem commonContact :
    leftSection P sB X e he ≫
        (Scheme.Modules.pullback (evaluationSquare P sB X e he)).map
          (movingPairContactLeft X.variety X.contact) =
      rightSection P sB X e he ≫
        (Scheme.Modules.pullback (evaluationSquare P sB X e he)).map
          (movingPairContactRight X.variety X.contact) := by
  rw [leftSection_contact, rightSection_contact]

end ParametrizedContact

namespace Curve

variable (P : ProjectiveLineOverC) {n : ℕ} (X : ContactFanoManifold n)
variable (f : RationalCurve P X.variety)

abbrev differential := differentialOver (projectiveLineVariety P) X.variety f.map f.overC

def leftRaw : AlgebraicSection
    (externalTensor P.structureMap
      (pullbackModule f.map (tangentSheaf X.variety.structureMap))
      (pullbackModule f.map X.contact.sequence.line.sheaf)) :=
  sourceBivector P ≫ externalTensorMap P.structureMap
    (differential P X f) (curveContactVelocity P X.contact f)

def rightRaw : AlgebraicSection
    (externalTensor P.structureMap
      (pullbackModule f.map X.contact.sequence.line.sheaf)
      (pullbackModule f.map (tangentSheaf X.variety.structureMap))) :=
  sourceBivector P ≫ externalTensorMap P.structureMap
    (curveContactVelocity P X.contact f) (differential P X f)

def leftSection : AlgebraicSection
    (pullbackModule (curveSquareMap P f) (movingPairBundleLeft X.variety X.contact)) :=
  leftRaw P X f ≫ curveExternalComparison P f
    (tangentSheaf X.variety.structureMap) X.contact.sequence.line.sheaf

def rightSection : AlgebraicSection
    (pullbackModule (curveSquareMap P f) (movingPairBundleRight X.variety X.contact)) :=
  rightRaw P X f ≫ curveExternalComparison P f
    X.contact.sequence.line.sheaf (tangentSheaf X.variety.structureMap)

theorem differential_comp (g : RationalCurve P X.variety)
    (e : ProjectiveLine ≅ ProjectiveLine)
    (he : e.hom ≫ P.structureMap = P.structureMap) (hg : g.map = e.hom ≫ f.map) :
    (SourceReparamProof.derivativeIso P e he).hom ≫
      (Scheme.Modules.pullback e.hom).map (differential P X f) ≫
        (compositionPullback e.hom f.map g.map hg.symm
          (tangentSheaf X.variety.structureMap)).hom = differential P X g := by
  rcases g with ⟨gm, hgm, hgn⟩
  change gm = e.hom ≫ f.map at hg
  subst gm
  simp only [compositionPullback, Iso.trans_hom, Iso.app_hom,
    eqToIso_refl, Iso.refl_hom, Category.comp_id]
  exact ContactDerivativeIsoProof.differentialOver_comp (projectiveLineVariety P)
    (projectiveLineVariety P) X.variety e.hom f.map he f.overC hgm

end Curve

namespace Reparametrization

variable (P : ProjectiveLineOverC) (e : ProjectiveLine ≅ ProjectiveLine)
variable (he : e.hom ≫ P.structureMap = P.structureMap)

abbrev curve := SourceReparamProof.isoCurve P e he

/-- Pullback of an external tensor with possibly different factors. -/
def mixedPull (E F : OModule ProjectiveLine)
    (B : AlgebraicSection (externalTensor P.structureMap E F)) :
    AlgebraicSection (externalTensor P.structureMap
      (pullbackModule e.hom E) (pullbackModule e.hom F)) := by
  letI := curveExternalComparison_isIso P (curve P e he) E F
  exact pullSection (curveSquareMap P (curve P e he)) B ≫
    inv (curveExternalComparison P (curve P e he) E F)

@[reassoc] theorem mixedPull_comparison (E F : OModule ProjectiveLine)
    (B : AlgebraicSection (externalTensor P.structureMap E F)) :
    mixedPull P e he E F B ≫ curveExternalComparison P (curve P e he) E F =
      pullSection (curveSquareMap P (curve P e he)) B := by
  letI := curveExternalComparison_isIso P (curve P e he) E F
  simp only [mixedPull, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

@[reassoc] theorem comparison_naturality {E E' F F' : OModule ProjectiveLine}
    (a : E ⟶ E') (b : F ⟶ F') :
    externalTensorMap P.structureMap ((Scheme.Modules.pullback e.hom).map a)
        ((Scheme.Modules.pullback e.hom).map b) ≫
        curveExternalComparison P (curve P e he) E' F' =
      curveExternalComparison P (curve P e he) E F ≫
        (Scheme.Modules.pullback (curveSquareMap P (curve P e he))).map
          (externalTensorMap P.structureMap a b) := by
  unfold curveExternalComparison externalTensorMap
  rw [← Category.assoc, ← tensorMap_comp]
  erw [pullbackSquare_naturality, pullbackSquare_naturality]
  rw [tensorMap_comp, Category.assoc, tensorPullback_naturality]
  simp only [Category.assoc]
  rfl

theorem mixedPull_map {E E' F F' : OModule ProjectiveLine}
    (a : E ⟶ E') (b : F ⟶ F')
    (B : AlgebraicSection (externalTensor P.structureMap E F)) :
    mixedPull P e he E' F' (B ≫ externalTensorMap P.structureMap a b) =
      mixedPull P e he E F B ≫ externalTensorMap P.structureMap
        ((Scheme.Modules.pullback e.hom).map a) ((Scheme.Modules.pullback e.hom).map b) := by
  letI := curveExternalComparison_isIso P (curve P e he) E' F'
  apply (cancel_mono (curveExternalComparison P (curve P e he) E' F')).mp
  rw [mixedPull_comparison, pullSection_naturality, Category.assoc,
    comparison_naturality, ← Category.assoc, mixedPull_comparison]

theorem mixedPull_source :
    mixedPull P e he (tangentSheaf P.structureMap) (tangentSheaf P.structureMap)
        (sourceBivector P) =
      sourceBivector P ≫ externalTensorMap P.structureMap
        (SourceReparamProof.derivativeIso P e he).hom
        (SourceReparamProof.derivativeIso P e he).hom :=
  SourceReparamProof.sourceBivector_curvePull P e he

theorem externalTensorMap_comp {Y : Scheme} (s : Y ⟶ ComplexBase)
    {E E' E'' F F' F'' : OModule Y}
    (a : E ⟶ E') (a' : E' ⟶ E'') (b : F ⟶ F') (b' : F' ⟶ F'') :
    externalTensorMap s a b ≫ externalTensorMap s a' b' =
      externalTensorMap s (a ≫ a') (b ≫ b') := by
  simp only [externalTensorMap, Functor.map_comp, tensorMap_comp]

variable {n : ℕ} (X : ContactFanoManifold n) (f g : RationalCurve P X.variety)
variable (hg : g.map = e.hom ≫ f.map)

/-- Reparametrization of the first actual mixed tensor, with the
derivative in its tangent factor. -/
theorem leftRaw :
    mixedPull P e he (pullbackModule f.map (tangentSheaf X.variety.structureMap))
        (pullbackModule f.map X.contact.sequence.line.sheaf) (Curve.leftRaw P X f) ≫
      externalTensorMap P.structureMap
        (compositionPullback e.hom f.map g.map hg.symm
          (tangentSheaf X.variety.structureMap)).hom
        (compositionPullback e.hom f.map g.map hg.symm X.contact.sequence.line.sheaf).hom =
      Curve.leftRaw P X g := by
  have hS : mixedPull P e he (identityCurveContact P).sequence.line.sheaf
      (identityCurveContact P).sequence.line.sheaf (sourceBivector P) =
      sourceBivector P ≫ externalTensorMap P.structureMap
        (SourceReparamProof.derivativeIso P e he).hom
        (SourceReparamProof.derivativeIso P e he).hom :=
    mixedPull_source P e he
  let qe := (SourceReparamProof.derivativeIso P e he).hom
  let qT := (Scheme.Modules.pullback e.hom).map (Curve.differential P X f)
  let qL := (Scheme.Modules.pullback e.hom).map (curveContactVelocity P X.contact f)
  let cT := (compositionPullback e.hom f.map g.map hg.symm
    (tangentSheaf X.variety.structureMap)).hom
  let cL := (compositionPullback e.hom f.map g.map hg.symm
    X.contact.sequence.line.sheaf).hom
  have hT : qe ≫ qT ≫ cT = Curve.differential P X g :=
    Curve.differential_comp P X f g e he hg
  have hL : qe ≫ qL ≫ cL = curveContactVelocity P X.contact g :=
    SourceReparamProof.curveContactVelocity_comp P X.contact f g e he hg
  have hmaps : externalTensorMap P.structureMap qe qe ≫
      externalTensorMap P.structureMap qT qL ≫
        externalTensorMap P.structureMap cT cL =
      externalTensorMap P.structureMap (qe ≫ qT ≫ cT) (qe ≫ qL ≫ cL) :=
    (congrArg (fun k => externalTensorMap P.structureMap qe qe ≫ k)
      (externalTensorMap_comp P.structureMap qT cT qL cL)).trans
        (externalTensorMap_comp P.structureMap qe (qT ≫ cT) qe (qL ≫ cL))
  rw [hT, hL] at hmaps
  rw [Curve.leftRaw, mixedPull_map, hS]
  calc
    _ = sourceBivector P ≫ (externalTensorMap P.structureMap qe qe ≫
        externalTensorMap P.structureMap qT qL ≫
          externalTensorMap P.structureMap cT cL) := by
      simp only [qe, qT, qL, cT, cL, Category.assoc]
    _ = sourceBivector P ≫ externalTensorMap P.structureMap
        (Curve.differential P X g) (curveContactVelocity P X.contact g) :=
      congrArg (fun k :
        externalTensor P.structureMap (tangentSheaf P.structureMap)
            (tangentSheaf P.structureMap) ⟶
          externalTensor P.structureMap (pullbackModule g.map (tangentSheaf X.variety.structureMap))
            (pullbackModule g.map X.contact.sequence.line.sheaf) =>
        sourceBivector P ≫ k) hmaps
    _ = Curve.leftRaw P X g := rfl

theorem rightRaw :
    mixedPull P e he (pullbackModule f.map X.contact.sequence.line.sheaf)
        (pullbackModule f.map (tangentSheaf X.variety.structureMap)) (Curve.rightRaw P X f) ≫
      externalTensorMap P.structureMap
        (compositionPullback e.hom f.map g.map hg.symm X.contact.sequence.line.sheaf).hom
        (compositionPullback e.hom f.map g.map hg.symm
          (tangentSheaf X.variety.structureMap)).hom =
      Curve.rightRaw P X g := by
  have hS : mixedPull P e he (identityCurveContact P).sequence.line.sheaf
      (identityCurveContact P).sequence.line.sheaf (sourceBivector P) =
      sourceBivector P ≫ externalTensorMap P.structureMap
        (SourceReparamProof.derivativeIso P e he).hom
        (SourceReparamProof.derivativeIso P e he).hom :=
    mixedPull_source P e he
  let qe := (SourceReparamProof.derivativeIso P e he).hom
  let qT := (Scheme.Modules.pullback e.hom).map (Curve.differential P X f)
  let qL := (Scheme.Modules.pullback e.hom).map (curveContactVelocity P X.contact f)
  let cT := (compositionPullback e.hom f.map g.map hg.symm
    (tangentSheaf X.variety.structureMap)).hom
  let cL := (compositionPullback e.hom f.map g.map hg.symm
    X.contact.sequence.line.sheaf).hom
  have hT : qe ≫ qT ≫ cT = Curve.differential P X g :=
    Curve.differential_comp P X f g e he hg
  have hL : qe ≫ qL ≫ cL = curveContactVelocity P X.contact g :=
    SourceReparamProof.curveContactVelocity_comp P X.contact f g e he hg
  have hmaps : externalTensorMap P.structureMap qe qe ≫
      externalTensorMap P.structureMap qL qT ≫
        externalTensorMap P.structureMap cL cT =
      externalTensorMap P.structureMap (qe ≫ qL ≫ cL) (qe ≫ qT ≫ cT) :=
    (congrArg (fun k => externalTensorMap P.structureMap qe qe ≫ k)
      (externalTensorMap_comp P.structureMap qL cL qT cT)).trans
        (externalTensorMap_comp P.structureMap qe (qL ≫ cL) qe (qT ≫ cT))
  rw [hL, hT] at hmaps
  rw [Curve.rightRaw, mixedPull_map, hS]
  calc
    _ = sourceBivector P ≫ (externalTensorMap P.structureMap qe qe ≫
        externalTensorMap P.structureMap qL qT ≫
          externalTensorMap P.structureMap cL cT) := by
      simp only [qe, qT, qL, cT, cL, Category.assoc]
    _ = sourceBivector P ≫ externalTensorMap P.structureMap
        (curveContactVelocity P X.contact g) (Curve.differential P X g) :=
      congrArg (fun k :
        externalTensor P.structureMap (tangentSheaf P.structureMap)
            (tangentSheaf P.structureMap) ⟶
          externalTensor P.structureMap (pullbackModule g.map X.contact.sequence.line.sheaf)
            (pullbackModule g.map (tangentSheaf X.variety.structureMap)) =>
        sourceBivector P ≫ k) hmaps
    _ = Curve.rightRaw P X g := rfl

end Reparametrization

end LeBrunSalamon.Construction.FamilyBivectors

end
