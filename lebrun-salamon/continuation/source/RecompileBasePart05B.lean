import RecompileBasePart05A

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


/-!
# Phase 28 -- actual external products, principal parts, and descent

This phase replaces the arbitrary external sheaf of the early candidate interfaces by p1*E tensor p2*F.
Global sections are ordinary O-module morphisms. Canonical pullback of the unit uses mathlib's ringed-site
map. Descent is stated only with adequate hypotheses; a proper dominant map alone does not make every
section descend.
-/

namespace LeBrunSalamon.PhaseTwentyEight

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseEight
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven

/-- Evaluation of an O_X-linear section at 1. -/
def sectionValue {X : Scheme} {E : OModule X}
    (s : AlgebraicSection E) : GlobalSections E :=
  Scheme.Modules.Hom.app s ⊤ (1 : RingSections X ⊤)

set_option backward.isDefEq.respectTransparency false in
def globalSectionFamilyEquiv {X : Scheme} (E : OModule X) :
    E.sections ≃ GlobalSections E where
  toFun s := s.val (Opposite.op ⊤)
  invFun a := ⟨fun U => E.presheaf.map (homOfLE le_top).op a, by
    intro U V i
    change E.presheaf.map i (E.presheaf.map (homOfLE le_top).op a) = _
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl⟩
  left_inv s := by
    apply PresheafOfModules.sections_ext
    intro U
    exact s.property (homOfLE le_top).op
  right_inv a := by
    change E.presheaf.map (𝟙 (Opposite.op (⊤ : X.Opens))) a = a
    simp

set_option backward.isDefEq.respectTransparency false in
theorem sectionValue_bijective {X : Scheme} (E : OModule X) :
    Function.Bijective (sectionValue (E := E)) :=
  (E.unitHomEquiv.trans (globalSectionFamilyEquiv E)).bijective

def sectionEquiv {X : Scheme} (E : OModule X) :
    AlgebraicSection E ≃ GlobalSections E :=
  Equiv.ofBijective _ (sectionValue_bijective E)

def sectionFromValue {X : Scheme} {E : OModule X}
    (v : GlobalSections E) : AlgebraicSection E :=
  (sectionEquiv E).symm v

set_option backward.isDefEq.respectTransparency false in
theorem sectionFromValue_spec {X : Scheme} {E : OModule X}
    (v : GlobalSections E) : sectionValue (sectionFromValue v) = v :=
  (sectionEquiv E).apply_symm_apply v

set_option backward.isDefEq.respectTransparency false in
/-- Canonical base-ring map; no arbitrary trivialization of f*O is chosen. -/
def unitPullbackMap {X Y : Scheme} (f : X ⟶ Y) :
    pullbackModule f (structureModule Y) ⟶ structureModule X :=
  SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom

set_option backward.isDefEq.respectTransparency false in
theorem unitPullbackMap_isIso {X Y : Scheme} (f : X ⟶ Y) :
    IsIso (unitPullbackMap f) := by
  let : (TopologicalSpace.Opens.map f.base).Final := inferInstance
  dsimp [unitPullbackMap]
  exact inferInstanceAs (IsIso (SheafOfModules.pullbackObjUnitToUnit
    (F := TopologicalSpace.Opens.map f.base) f.toRingCatSheafHom))

def unitPullbackIso {X Y : Scheme} (f : X ⟶ Y) :
    pullbackModule f (structureModule Y) ≅ structureModule X := by
  letI := unitPullbackMap_isIso f
  exact asIso (unitPullbackMap f)

def pullSection {X Y : Scheme} (f : X ⟶ Y)
    {E : OModule Y} (s : AlgebraicSection E) :
    AlgebraicSection (pullbackModule f E) :=
  (unitPullbackIso f).inv ≫ restrictSection f s

def tensorSection {X : Scheme} {E F : OModule X}
    (a : AlgebraicSection E) (b : AlgebraicSection F) :
    AlgebraicSection (tensorSheaf E F) :=
  sectionFromValue ((tensorPresentation E F).pair.apply ⊤
    (sectionValue a) (sectionValue b))

/-! Additive sections and their actual tensor pairing. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix

@[simp]
theorem sectionValue_add {X : Scheme} {E : OModule X}
    (s t : AlgebraicSection E) : sectionValue (s + t) = sectionValue s + sectionValue t := rfl

@[simp]
theorem sectionValue_zero {X : Scheme} (E : OModule X) :
    sectionValue (0 : AlgebraicSection E) = 0 := rfl

@[simp]
theorem sectionValue_neg {X : Scheme} {E : OModule X}
    (s : AlgebraicSection E) : sectionValue (-s) = -sectionValue s := rfl

/-- The established section equivalence respects the actual additive structures. -/
def sectionAddEquiv {X : Scheme} (E : OModule X) :
    AlgebraicSection E ≃+ GlobalSections E where
  toEquiv := sectionEquiv E
  map_add' := sectionValue_add

@[simp]
theorem sectionFromValue_add {X : Scheme} {E : OModule X}
    (v w : GlobalSections E) :
    sectionFromValue (v + w) = sectionFromValue v + sectionFromValue w := by
  apply (sectionValue_bijective E).injective
  simp only [sectionValue_add, sectionFromValue_spec]

@[simp]
theorem sectionFromValue_zero {X : Scheme} (E : OModule X) :
    sectionFromValue (0 : GlobalSections E) = 0 := by
  apply (sectionValue_bijective E).injective
  simp only [sectionValue_zero, sectionFromValue_spec]

@[simp]
theorem sectionFromValue_neg {X : Scheme} {E : OModule X}
    (v : GlobalSections E) : sectionFromValue (-v) = -sectionFromValue v := by
  apply (sectionValue_bijective E).injective
  simp only [sectionValue_neg, sectionFromValue_spec]

@[simp]
theorem sectionFromValue_sectionValue {X : Scheme} {E : OModule X}
    (s : AlgebraicSection E) : sectionFromValue (sectionValue s) = s :=
  (sectionEquiv E).symm_apply_apply s

/-- Evaluation at one commutes with the actual map of module sheaves. -/
@[simp]
theorem sectionValue_comp {X : Scheme} {E F : OModule X}
    (s : AlgebraicSection E) (f : E ⟶ F) :
    sectionValue (s ≫ f) = f.app ⊤ (sectionValue s) := rfl

@[simp]
theorem sectionValue_tensorSection {X : Scheme} {E F : OModule X}
    (a : AlgebraicSection E) (b : AlgebraicSection F) :
    sectionValue (tensorSection a b) =
      (tensorPresentation E F).pair.apply ⊤ (sectionValue a) (sectionValue b) :=
  sectionFromValue_spec _









theorem tensorSection_neg_left {X : Scheme} {E F : OModule X}
    (a : AlgebraicSection E) (b : AlgebraicSection F) :
    tensorSection (-a) b = -tensorSection a b := by
  apply (sectionValue_bijective (tensorSheaf E F)).injective
  simp only [sectionValue_neg, sectionValue_tensorSection, map_neg, LinearMap.neg_apply]

theorem tensorSection_neg_right {X : Scheme} {E F : OModule X}
    (a : AlgebraicSection E) (b : AlgebraicSection F) :
    tensorSection a (-b) = -tensorSection a b := by
  apply (sectionValue_bijective (tensorSheaf E F)).injective
  simp only [sectionValue_neg, sectionValue_tensorSection, map_neg]

/-- The section tensor product respects the already chosen tensor-map convention. -/
theorem tensorSection_map {X : Scheme} {E E' F F' : OModule X}
    (f : E ⟶ E') (g : F ⟶ F')
    (a : AlgebraicSection E) (b : AlgebraicSection F) :
    tensorSection a b ≫ tensorMap f g = tensorSection (a ≫ f) (b ≫ g) := by
  apply (sectionValue_bijective (tensorSheaf E' F')).injective
  simp only [sectionValue_comp, sectionValue_tensorSection, tensorMap_apply]

end

set_option backward.isDefEq.respectTransparency false in
theorem tensorSection_add_left {X : Scheme} {E F : OModule X}
    (a a' : AlgebraicSection E) (b : AlgebraicSection F) :
    tensorSection (a + a') b = tensorSection a b + tensorSection a' b := by
  apply (sectionValue_bijective (tensorSheaf E F)).injective
  simp only [sectionValue_add, sectionValue_tensorSection, map_add, LinearMap.add_apply]

set_option backward.isDefEq.respectTransparency false in
theorem tensorSection_add_right {X : Scheme} {E F : OModule X}
    (a : AlgebraicSection E) (b b' : AlgebraicSection F) :
    tensorSection a (b + b') = tensorSection a b + tensorSection a b' := by
  apply (sectionValue_bijective (tensorSheaf E F)).injective
  simp only [sectionValue_add, sectionValue_tensorSection, map_add]

set_option backward.isDefEq.respectTransparency false in
theorem tensorSection_zero_left {X : Scheme} {E F : OModule X}
    (b : AlgebraicSection F) : tensorSection (0 : AlgebraicSection E) b = 0 := by
  apply (sectionValue_bijective (tensorSheaf E F)).injective
  simp only [sectionValue_zero, sectionValue_tensorSection, map_zero, LinearMap.zero_apply]

set_option backward.isDefEq.respectTransparency false in
theorem tensorSection_zero_right {X : Scheme} {E F : OModule X}
    (a : AlgebraicSection E) : tensorSection a (0 : AlgebraicSection F) = 0 := by
  apply (sectionValue_bijective (tensorSheaf E F)).injective
  simp only [sectionValue_zero, sectionValue_tensorSection, map_zero]

def externalTensor {X : Scheme} (s : X ⟶ ComplexBase)
    (E F : OModule X) : OModule (SelfProduct s) :=
  tensorSheaf (pullbackModule (firstProjection s) E)
    (pullbackModule (secondProjection s) F)

def externalSquareLine {X : Scheme} (s : X ⟶ ComplexBase)
    (L : LineBundle X) : LineBundle (SelfProduct s) :=
  tensorLine (pullbackLine (firstProjection s) L)
    (pullbackLine (secondProjection s) L)

def externalProductSection {X : Scheme} (s : X ⟶ ComplexBase)
    {E F : OModule X} (a : AlgebraicSection E) (b : AlgebraicSection F) :
    AlgebraicSection (externalTensor s E F) :=
  tensorSection (pullSection (firstProjection s) a)
    (pullSection (secondProjection s) b)

def externalTensorMap {X : Scheme} (s : X ⟶ ComplexBase)
    {E E' F F' : OModule X} (f : E ⟶ E') (g : F ⟶ F') :
    externalTensor s E F ⟶ externalTensor s E' F' :=
  tensorMap ((Scheme.Modules.pullback (firstProjection s)).map f)
    ((Scheme.Modules.pullback (secondProjection s)).map g)

set_option backward.isDefEq.respectTransparency false in
theorem externalTensorMap_id {X : Scheme} (s : X ⟶ ComplexBase)
    (E F : OModule X) :
    externalTensorMap s (𝟙 E) (𝟙 F) = 𝟙 (externalTensor s E F) := by
  unfold externalTensorMap
  rw [(Scheme.Modules.pullback (firstProjection s)).map_id,
    (Scheme.Modules.pullback (secondProjection s)).map_id]
  exact tensorMap_id _ _

theorem externalTensor_diagonal {X : Scheme} (s : X ⟶ ComplexBase)
    (E F : OModule X) :
    Nonempty (pullbackModule (diagonal s) (externalTensor s E F) ≅
      tensorSheaf E F) := by
  obtain ⟨t⟩ := tensorSheaf_pullback (diagonal s)
    (pullbackModule (firstProjection s) E) (pullbackModule (secondProjection s) F)
  let e : pullbackModule (diagonal s) (pullbackModule (firstProjection s) E) ≅ E :=
    (Scheme.Modules.pullbackComp (diagonal s) (firstProjection s)).app E ≪≫
      (Scheme.Modules.pullbackCongr (pullback.diagonal_fst s)).app E ≪≫
        (Scheme.Modules.pullbackId X).app E
  let f : pullbackModule (diagonal s) (pullbackModule (secondProjection s) F) ≅ F :=
    (Scheme.Modules.pullbackComp (diagonal s) (secondProjection s)).app F ≪≫
      (Scheme.Modules.pullbackCongr (pullback.diagonal_snd s)).app F ≪≫
        (Scheme.Modules.pullbackId X).app F
  exact ⟨t ≪≫ tensorIso e f⟩

theorem externalSquare_diagonal {X : Scheme} (s : X ⟶ ComplexBase)
    (L : LineBundle X) :
    Nonempty (pullbackModule (diagonal s) (externalSquareLine s L).sheaf ≅
      (linePower L 2).sheaf) := by
  obtain ⟨e⟩ := externalTensor_diagonal s L.sheaf L.sheaf
  change Nonempty (pullbackModule (diagonal s) (externalTensor s L.sheaf L.sheaf) ≅
    tensorSheaf (tensorSheaf (structureModule X) L.sheaf) L.sheaf)
  exact ⟨e ≪≫ tensorIso (TensorConstruction.leftUnitIso L.sheaf).symm (Iso.refl _)⟩

/-- An exchange identification must be involutive on sections. A bare
isomorphism tau*E ≅ E need not satisfy that condition. -/
structure InvolutiveExternalExchange {X : Scheme}
    (s : X ⟶ ComplexBase) (L : LineBundle X) where
  identification : TwoPointExchangeIdentification s (externalSquareLine s L).sheaf
  unitNormalization : identification.onUnit = unitPullbackIso (swapSelfProduct s)
  involutive : ∀ B : AlgebraicSection (externalSquareLine s L).sheaf,
    identification.swapSection (identification.swapSection B) = B
  onProducts : ∀ a b : AlgebraicSection L.sheaf,
    identification.swapSection (externalProductSection s a b) =
      externalProductSection s b a

/-- The canonical structure-sheaf comparison O_Y -> f_* O_X. -/
def structurePushforwardMap {X Y : Scheme} (f : X ⟶ Y) :
    structureModule Y ⟶ (Scheme.Modules.pushforward f).obj (structureModule X) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

set_option backward.isDefEq.respectTransparency false in
theorem unitPullbackMap_adjoint {X Y : Scheme} (f : X ⟶ Y) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      (unitPullbackMap f) = structurePushforwardMap f :=
  SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    f.toRingCatSheafHom

set_option backward.isDefEq.respectTransparency false in
theorem unitPullbackMap_pullSection {X Y : Scheme} (f : X ⟶ Y)
    {E : OModule Y} (s : AlgebraicSection E) :
    unitPullbackMap f ≫ pullSection f s = (Scheme.Modules.pullback f).map s := by
  change (unitPullbackIso f).hom ≫ (unitPullbackIso f).inv ≫ _ = _
  simp [restrictSection]

set_option backward.isDefEq.respectTransparency false in
theorem pullSection_adjoint {X Y : Scheme} (f : X ⟶ Y)
    {E : OModule Y} (s : AlgebraicSection E) :
    structurePushforwardMap f ≫ (Scheme.Modules.pushforward f).map (pullSection f s) =
      s ≫ (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  calc
    _ = adj.homEquiv _ _ (unitPullbackMap f ≫ pullSection f s) := by
      rw [adj.homEquiv_naturality_right, unitPullbackMap_adjoint]
    _ = adj.homEquiv _ _ ((Scheme.Modules.pullback f).map s) := by
      rw [unitPullbackMap_pullSection]
    _ = _ := by
      rw [adj.homEquiv_apply]
      exact (adj.unit.naturality s).symm

set_option backward.isDefEq.respectTransparency false in
theorem structurePushforwardMap_one {X Y : Scheme} (f : X ⟶ Y) :
    (structurePushforwardMap f).app ⊤ (1 : RingSections Y ⊤) = (1 : RingSections X ⊤) := by
  change f.appTop (1 : RingSections Y ⊤) = 1
  exact map_one f.appTop.hom

set_option backward.isDefEq.respectTransparency false in
theorem pullSection_value {X Y : Scheme} (f : X ⟶ Y)
    {E : OModule Y} (s : AlgebraicSection E) :
    sectionValue (pullSection f s) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E).app ⊤
        (sectionValue s) := by
  have h := congrArg (fun k => k.app ⊤ (1 : RingSections Y ⊤)) (pullSection_adjoint f s)
  change Scheme.Modules.Hom.app (pullSection f s) ⊤ (f.appTop (1 : RingSections Y ⊤)) =
    Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E) ⊤
      (Scheme.Modules.Hom.app s ⊤ (1 : RingSections Y ⊤)) at h
  rw [show f.appTop (1 : RingSections Y ⊤) = 1 from map_one f.appTop.hom] at h
  exact h




end LeBrunSalamon.PhaseTwentyEight

namespace LeBrunSalamon.Skeleton

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton

/-- The adjunction UNIT pulls a section on U back to f^{-1}U. -/
def pullLocalSection {X Y : Scheme} (f : X ⟶ Y) (E : OModule Y)
    (U : Y.Opens) (e : SectionsOn E U) :
    SectionsOn (pullbackModule f E) (f ⁻¹ᵁ U) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E).app U e

/-- Characterization on local pure tensors fixes the normalization of
base change. Naturality then determines its value on smaller opens. -/
def IsPullbackPair {X Y : Scheme} (f : X ⟶ Y)
    {E F G : OModule Y} (b : SheafBilinearMap E F G)
    (q : SheafBilinearMap (pullbackModule f E)
      (pullbackModule f F) (pullbackModule f G)) : Prop :=
  ∀ (U : Y.Opens) (e : SectionsOn E U) (z : SectionsOn F U),
    q.apply (f ⁻¹ᵁ U) (pullLocalSection f E U e) (pullLocalSection f F U z) =
      pullLocalSection f G U (b.apply U e z)

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton

namespace PullbackPairProof

theorem pullLocalSection_add {X Y : Scheme} (f : X ⟶ Y) (E : OModule Y)
    (U : Y.Opens) (e z : SectionsOn E U) :
    pullLocalSection f E U (e + z) =
      pullLocalSection f E U e + pullLocalSection f E U z := by
  exact (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E).app U).hom.map_add e z

/-- The coefficient action is exactly the actual structure-sheaf map. -/
theorem pullLocalSection_smul {X Y : Scheme} (f : X ⟶ Y) (E : OModule Y)
    (U : Y.Opens) (r : RingSections Y U) (e : SectionsOn E U) :
    pullLocalSection f E U (r • e) = f.app U r • pullLocalSection f E U e := by
  exact Scheme.Modules.Hom.app_smul
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E) r e

theorem pullLocalSection_restrict {X Y : Scheme} (f : X ⟶ Y) (E : OModule Y)
    {U V : Y.Opens} (i : V ⟶ U) (e : SectionsOn E U) :
    (pullbackModule f E).presheaf.map ((TopologicalSpace.Opens.map f.base).map i).op
        (pullLocalSection f E U e) =
      pullLocalSection f E V (E.presheaf.map i.op e) := by
  exact sheafHom_naturality ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E) i e

/-- A map out of the actual pullback is fixed by its action on all unit images. -/
theorem pullbackHom_ext {X Y : Scheme} (f : X ⟶ Y) (E : OModule Y) (H : OModule X)
    (a b : pullbackModule f E ⟶ H)
    (h : ∀ (U : Y.Opens) (e : SectionsOn E U),
      a.app (f ⁻¹ᵁ U) (pullLocalSection f E U e) =
        b.app (f ⁻¹ᵁ U) (pullLocalSection f E U e)) : a = b := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv E H).injective
  apply Scheme.Modules.hom_ext
  intro U
  ext e
  exact h U e

/-- The genuine right adjoint to restriction to the site over V. -/
abbrev restrictionPushforward {X : Scheme} (H : OModule X) (V : X.Opens) : OModule X :=
  (SheafOfModules.pushforward
    (SheafOfModules.pushforwardOver (R := X.ringCatSheaf) V)).obj (H.over V)

def localHomAdjunct {X : Scheme} {M H : OModule X} {V : X.Opens}
    (a : M.over V ⟶ H.over V) : M ⟶ restrictionPushforward H V :=
  (SheafOfModules.overPushforwardOverAdj (R := X.ringCatSheaf) V).homEquiv M (H.over V) a

theorem localHomAdjunct_apply {X : Scheme} {M H : OModule X} {V : X.Opens}
    (a : M.over V ⟶ H.over V) (W : X.Opens) (e : SectionsOn M W) :
    (localHomAdjunct a).app W e =
      a.val.app (op ((Over.star V).obj W))
        (M.val.map ((Over.forgetAdjStar V).counit.app W).op e) := rfl

/-- Restricted unit images on intersections determine every local map.
No assertion that global sections generate the pullback is required. -/
theorem localPullbackHom_ext {X Y : Scheme} (f : X ⟶ Y) (E : OModule Y)
    (H : OModule X) (V : X.Opens)
    (a b : (pullbackModule f E).over V ⟶ H.over V)
    (h : ∀ (U : Y.Opens) (e : SectionsOn E U),
      a.val.app (op ((Over.star V).obj (f ⁻¹ᵁ U)))
          ((pullbackModule f E).val.map
            ((Over.forgetAdjStar V).counit.app (f ⁻¹ᵁ U)).op (pullLocalSection f E U e)) =
        b.val.app (op ((Over.star V).obj (f ⁻¹ᵁ U)))
          ((pullbackModule f E).val.map
            ((Over.forgetAdjStar V).counit.app (f ⁻¹ᵁ U)).op (pullLocalSection f E U e))) :
    a = b := by
  apply ((SheafOfModules.overPushforwardOverAdj (R := X.ringCatSheaf) V).homEquiv
    (pullbackModule f E) (H.over V)).injective
  apply pullbackHom_ext f E (restrictionPushforward H V)
  intro U e
  change (localHomAdjunct a).app (f ⁻¹ᵁ U) (pullLocalSection f E U e) =
    (localHomAdjunct b).app (f ⁻¹ᵁ U) (pullLocalSection f E U e)
  rw [localHomAdjunct_apply, localHomAdjunct_apply]
  exact h U e

end PullbackPairProof

end

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton

namespace PullbackPairProof

def preimageProductIso {X Y : Scheme} (f : X ⟶ Y) (U W : Y.Opens) :
    (f ⁻¹ᵁ (U ⨯ W)) ≅ (f ⁻¹ᵁ U) ⨯ (f ⁻¹ᵁ W) :=
  PreservesLimitPair.iso (TopologicalSpace.Opens.map f.base) U W

theorem preimageProduct_scalar {X Y : Scheme} (f : X ⟶ Y)
    (U W : Y.Opens) (r : RingSections Y W) :
    X.presheaf.map (preimageProductIso f U W).inv.op
        (f.app (U ⨯ W) (Y.presheaf.map (prod.snd : U ⨯ W ⟶ W).op r)) =
      X.presheaf.map (prod.snd : (f ⁻¹ᵁ U) ⨯ (f ⁻¹ᵁ W) ⟶ (f ⁻¹ᵁ W)).op
        (f.app W r) := by
  have hn := congrArg (fun a => a r) (f.naturality (prod.snd : U ⨯ W ⟶ W).op)
  change f.app (U ⨯ W) (Y.presheaf.map (prod.snd : U ⨯ W ⟶ W).op r) =
    X.presheaf.map ((TopologicalSpace.Opens.map f.base).map
      (prod.snd : U ⨯ W ⟶ W)).op (f.app W r) at hn
  rw [hn, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  congr 1

/-- Restriction pushforward commutes with the actual scheme pushforward.
This is a normalized comparison, with coefficient action checked explicitly. -/
def restrictionPushforwardComparison {X Y : Scheme} (f : X ⟶ Y)
    (H : OModule X) (U : Y.Opens) :
    restrictionPushforward ((Scheme.Modules.pushforward f).obj H) U ⟶
      (Scheme.Modules.pushforward f).obj (restrictionPushforward H (f ⁻¹ᵁ U)) where
  val :=
    { app W :=
        ConcreteCategory.ofHom (C := ModuleCat (Y.ringCatSheaf.obj.obj W))
          (X := (restrictionPushforward ((Scheme.Modules.pushforward f).obj H) U).val.obj W)
          (Y := ((Scheme.Modules.pushforward f).obj
            (restrictionPushforward H (f ⁻¹ᵁ U))).val.obj W)
          { toFun := H.presheaf.map (preimageProductIso f U W.unop).inv.op
            map_add' := (H.presheaf.map (preimageProductIso f U W.unop).inv.op).hom.map_add
            map_smul' := by
              intro r e
              change RingSections Y W.unop at r
              change SectionsOn H (f ⁻¹ᵁ (U ⨯ W.unop)) at e
              change H.presheaf.map (preimageProductIso f U W.unop).inv.op
                  (f.app (U ⨯ W.unop)
                    (Y.presheaf.map (prod.snd : U ⨯ W.unop ⟶ W.unop).op r) • e) =
                X.presheaf.map
                  (prod.snd : (f ⁻¹ᵁ U) ⨯ (f ⁻¹ᵁ W.unop) ⟶ (f ⁻¹ᵁ W.unop)).op
                  (f.app W.unop r) •
                  H.presheaf.map (preimageProductIso f U W.unop).inv.op e
              rw [Scheme.Modules.map_smul, preimageProduct_scalar] }
      naturality := by
        intro W V i
        ext e
        have hn : ∀ e' : SectionsOn H (f ⁻¹ᵁ (U ⨯ W.unop)),
            H.presheaf.map (preimageProductIso f U V.unop).inv.op
                (H.presheaf.map ((TopologicalSpace.Opens.map f.base).map
                  ((Over.star U).map i.unop).left).op e') =
              H.presheaf.map
                ((Over.star (f ⁻¹ᵁ U)).map
                  ((TopologicalSpace.Opens.map f.base).map i.unop)).left.op
                (H.presheaf.map (preimageProductIso f U W.unop).inv.op e') := by
          intro e'
          have hm :
              H.presheaf.map ((TopologicalSpace.Opens.map f.base).map
                  ((Over.star U).map i.unop).left).op ≫
                  H.presheaf.map (preimageProductIso f U V.unop).inv.op =
                H.presheaf.map (preimageProductIso f U W.unop).inv.op ≫
                  H.presheaf.map ((Over.star (f ⁻¹ᵁ U)).map
                    ((TopologicalSpace.Opens.map f.base).map i.unop)).left.op := by
            rw [← Functor.map_comp, ← Functor.map_comp]
            congr 1
          exact congrArg (fun k : H.presheaf.obj (op (f ⁻¹ᵁ (U ⨯ W.unop))) ⟶
              H.presheaf.obj (op ((f ⁻¹ᵁ U) ⨯ (f ⁻¹ᵁ V.unop))) => k e') hm
        exact hn e }

instance restrictionPushforwardComparison_isIso {X Y : Scheme} (f : X ⟶ Y)
    (H : OModule X) (U : Y.Opens) : IsIso (restrictionPushforwardComparison f H U) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro W
  have hmap : (restrictionPushforwardComparison f H U).app W =
      H.presheaf.map (preimageProductIso f U W).inv.op := by
    ext e
    rfl
  rw [hmap]
  infer_instance

/-- The local form of the original pullback/pushforward adjunction. -/
def localPullbackHomEquiv {X Y : Scheme} (f : X ⟶ Y)
    (E : OModule Y) (H : OModule X) (U : Y.Opens) :
    ((pullbackModule f E).over (f ⁻¹ᵁ U) ⟶ H.over (f ⁻¹ᵁ U)) ≃
      (E.over U ⟶ ((Scheme.Modules.pushforward f).obj H).over U) :=
  ((SheafOfModules.overPushforwardOverAdj (R := X.ringCatSheaf) (f ⁻¹ᵁ U)).homEquiv
    (pullbackModule f E) (H.over (f ⁻¹ᵁ U))).trans
    (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv E
      (restrictionPushforward H (f ⁻¹ᵁ U))).trans
      ((Iso.homCongr (Iso.refl E) (asIso (restrictionPushforwardComparison f H U)).symm).trans
        ((SheafOfModules.overPushforwardOverAdj (R := Y.ringCatSheaf) U).homEquiv E
          (((Scheme.Modules.pushforward f).obj H).over U)).symm))

end PullbackPairProof

end

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton

namespace PullbackPairProof

theorem restrictionPushforwardComparison_inv_app {X Y : Scheme} (f : X ⟶ Y)
    (H : OModule X) (U W : Y.Opens)
    (e : SectionsOn H ((f ⁻¹ᵁ U) ⨯ (f ⁻¹ᵁ W))) :
    (inv (restrictionPushforwardComparison f H U)).app W e =
      H.presheaf.map (preimageProductIso f U W).hom.op e := by
  rw [Scheme.Modules.inv_app]
  have hmap : (restrictionPushforwardComparison f H U).app W =
      H.presheaf.map (preimageProductIso f U W).inv.op := by
    ext z
    rfl
  have he : inv ((restrictionPushforwardComparison f H U).app W) =
      H.presheaf.map (preimageProductIso f U W).hom.op := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [hmap, ← CategoryTheory.Functor.map_comp, ← op_comp, Iso.hom_inv_id]
    exact CategoryTheory.Functor.map_id H.presheaf (op (f ⁻¹ᵁ (U ⨯ W)))
  exact congrArg (fun k : H.presheaf.obj (op ((f ⁻¹ᵁ U) ⨯ (f ⁻¹ᵁ W))) ⟶
      H.presheaf.obj (op (f ⁻¹ᵁ (U ⨯ W))) => k e) he

/-- Restricting a local map to the actual unit images gives a local map on Y. -/
def localUnitPrecompose {X Y : Scheme} (f : X ⟶ Y) (E : OModule Y) (H : OModule X)
    (U : Y.Opens)
    (a : (pullbackModule f E).over (f ⁻¹ᵁ U) ⟶ H.over (f ⁻¹ᵁ U)) :
    E.over U ⟶ ((Scheme.Modules.pushforward f).obj H).over U where
  val :=
    { app W := ModuleCat.ofHom
        { toFun := fun e =>
            a.val.app (op ((Over.post (TopologicalSpace.Opens.map f.base)).obj W.unop))
              (pullLocalSection f E W.unop.left e)
          map_add' := by
            intro e z
            rw [pullLocalSection_add, map_add]
          map_smul' := by
            intro r e
            change a.val.app (op ((Over.post (TopologicalSpace.Opens.map f.base)).obj W.unop))
                (pullLocalSection f E W.unop.left (r • e)) =
              f.app W.unop.left r •
                a.val.app (op ((Over.post (TopologicalSpace.Opens.map f.base)).obj W.unop))
                  (pullLocalSection f E W.unop.left e)
            rw [pullLocalSection_smul]
            exact (a.val.app _).hom.map_smul _ _ }
      naturality := by
        intro W V i
        ext e
        change a.val.app (op ((Over.post (TopologicalSpace.Opens.map f.base)).obj V.unop))
            (pullLocalSection f E V.unop.left (E.val.map i.unop.left.op e)) =
          H.val.map ((TopologicalSpace.Opens.map f.base).map i.unop.left).op
            (a.val.app (op ((Over.post (TopologicalSpace.Opens.map f.base)).obj W.unop))
              (pullLocalSection f E W.unop.left e))
        have hr := pullLocalSection_restrict f E i.unop.left e
        change (pullbackModule f E).val.map
            ((TopologicalSpace.Opens.map f.base).map i.unop.left).op
            (pullLocalSection f E W.unop.left e) =
          pullLocalSection f E V.unop.left (E.val.map i.unop.left.op e) at hr
        rw [← hr]
        exact PresheafOfModules.naturality_apply a.val
          ((Over.post (TopologicalSpace.Opens.map f.base)).map i.unop).op
          (pullLocalSection f E W.unop.left e) }

/-- The abstract local equivalence has precisely the unit-precomposition formula. -/
theorem localPullbackHomEquiv_eq_unitPrecompose {X Y : Scheme} (f : X ⟶ Y)
    (E : OModule Y) (H : OModule X) (U : Y.Opens)
    (a : (pullbackModule f E).over (f ⁻¹ᵁ U) ⟶ H.over (f ⁻¹ᵁ U)) :
    localPullbackHomEquiv f E H U a = localUnitPrecompose f E H U a := by
  letI : IsIso (restrictionPushforwardComparison f H U) :=
    restrictionPushforwardComparison_isIso f H U
  apply ((SheafOfModules.overPushforwardOverAdj (R := Y.ringCatSheaf) U).homEquiv
    E (((Scheme.Modules.pushforward f).obj H).over U)).injective
  simp only [localPullbackHomEquiv, Equiv.trans_apply,
    Iso.homCongr_apply, Iso.refl_inv, Category.id_comp]
  trans ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv E
    (restrictionPushforward H (f ⁻¹ᵁ U))) (localHomAdjunct a) ≫
      inv (restrictionPushforwardComparison f H U)
  · exact ((SheafOfModules.overPushforwardOverAdj (R := Y.ringCatSheaf) U).homEquiv
      E (((Scheme.Modules.pushforward f).obj H).over U)).apply_symm_apply _
  rw [Adjunction.homEquiv_unit]
  apply Scheme.Modules.hom_ext
  intro W
  ext e
  change (inv (restrictionPushforwardComparison f H U)).app W
      ((localHomAdjunct a).app (f ⁻¹ᵁ W) (pullLocalSection f E W e)) =
    a.val.app (op ((Over.post (TopologicalSpace.Opens.map f.base)).obj ((Over.star U).obj W)))
      (pullLocalSection f E (U ⨯ W)
        (E.val.map ((Over.forgetAdjStar U).counit.app W).op e))
  rw [restrictionPushforwardComparison_inv_app, localHomAdjunct_apply]
  let unitW : SectionsOn (pullbackModule f E) (f ⁻¹ᵁ W) := pullLocalSection f E W e
  let m : SectionsOn (pullbackModule f E) ((f ⁻¹ᵁ U) ⨯ (f ⁻¹ᵁ W)) :=
    (pullbackModule f E).val.map
      ((Over.forgetAdjStar (f ⁻¹ᵁ U)).counit.app (f ⁻¹ᵁ W)).op unitW
  have hr : (pullbackModule f E).val.map
        ((TopologicalSpace.Opens.map f.base).map
          ((Over.forgetAdjStar U).counit.app W)).op unitW =
      pullLocalSection f E (U ⨯ W)
        (E.val.map ((Over.forgetAdjStar U).counit.app W).op e) :=
    pullLocalSection_restrict f E ((Over.forgetAdjStar U).counit.app W) e
  have hcomp :
      ((Over.forgetAdjStar (f ⁻¹ᵁ U)).counit.app (f ⁻¹ᵁ W)).op ≫
          (preimageProductIso f U W).hom.op =
        ((TopologicalSpace.Opens.map f.base).map
          ((Over.forgetAdjStar U).counit.app W)).op :=
    Subsingleton.elim _ _
  have hinput : (pullbackModule f E).val.map (preimageProductIso f U W).hom.op m =
      pullLocalSection f E (U ⨯ W)
        (E.val.map ((Over.forgetAdjStar U).counit.app W).op e) :=
    ((pullbackModule f E).val.map_comp_apply
      ((Over.forgetAdjStar (f ⁻¹ᵁ U)).counit.app (f ⁻¹ᵁ W)).op
      (preimageProductIso f U W).hom.op unitW).symm.trans
        (((pullbackModule f E).val.congr_map_apply hcomp unitW).trans hr)
  let j : (Over.post (TopologicalSpace.Opens.map f.base)).obj ((Over.star U).obj W) ⟶
      (Over.star (f ⁻¹ᵁ U)).obj (f ⁻¹ᵁ W) :=
    Over.homMk (preimageProductIso f U W).hom (Subsingleton.elim _ _)
  have hn := PresheafOfModules.naturality_apply a.val j.op m
  have hout := congrArg (fun x : SectionsOn (pullbackModule f E) (f ⁻¹ᵁ (U ⨯ W)) =>
    a.val.app (op ((Over.post (TopologicalSpace.Opens.map f.base)).obj
      ((Over.star U).obj W))) x) hinput
  exact hn.symm.trans hout

theorem localUnitPrecompose_bijective {X Y : Scheme} (f : X ⟶ Y)
    (E : OModule Y) (H : OModule X) (U : Y.Opens) :
    Function.Bijective (localUnitPrecompose f E H U) := by
  have he : localUnitPrecompose f E H U = localPullbackHomEquiv f E H U := by
    funext a
    exact (localPullbackHomEquiv_eq_unitPrecompose f E H U a).symm
  rw [he]
  exact (localPullbackHomEquiv f E H U).bijective

end PullbackPairProof

end

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton

namespace PullbackPairProof

def localBilinearInput {X Y : Scheme} (f : X ⟶ Y)
    {E F G : OModule Y} (b : SheafBilinearMap E F G)
    (U : Y.Opens) (e : SectionsOn E U) :
    F.over U ⟶ ((Scheme.Modules.pushforward f).obj (pullbackModule f G)).over U :=
  HomConstruction.sectionOverEquiv F G U (HomConstruction.localCurry b U e) ≫
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).over U

def localBilinearLift {X Y : Scheme} (f : X ⟶ Y)
    {E F G : OModule Y} (b : SheafBilinearMap E F G)
    (U : Y.Opens) (e : SectionsOn E U) :
    HomConstruction.Section (pullbackModule f F) (pullbackModule f G) (f ⁻¹ᵁ U) :=
  (HomConstruction.sectionOverEquiv (pullbackModule f F) (pullbackModule f G) (f ⁻¹ᵁ U)).symm
    ((localPullbackHomEquiv f F (pullbackModule f G) U).symm (localBilinearInput f b U e))

/-- The extension acts on the original local pure input with its exact coefficient. -/
theorem localBilinearLift_unit {X Y : Scheme} (f : X ⟶ Y)
    {E F G : OModule Y} (b : SheafBilinearMap E F G)
    (U : Y.Opens) (e : SectionsOn E U) (W : Over U) (z : SectionsOn F W.left) :
    (localBilinearLift f b U e).app
        (op ((Over.post (TopologicalSpace.Opens.map f.base)).obj W))
        (pullLocalSection f F W.left z) =
      pullLocalSection f G W.left (b.apply W.left (E.val.map W.hom.op e) z) := by
  have h := (localPullbackHomEquiv f F (pullbackModule f G) U).apply_symm_apply
    (localBilinearInput f b U e)
  rw [localPullbackHomEquiv_eq_unitPrecompose] at h
  exact congrArg (fun a : F.over U ⟶
      ((Scheme.Modules.pushforward f).obj (pullbackModule f G)).over U =>
      a.val.app (op W) z) h

/-- The normalized local adjunction determines sections of the actual Hom sheaf. -/
theorem localSection_ext {X Y : Scheme} (f : X ⟶ Y) (E : OModule Y)
    (H : OModule X) (U : Y.Opens)
    (a b : HomConstruction.Section (pullbackModule f E) H (f ⁻¹ᵁ U))
    (h : ∀ (W : Over U) (e : SectionsOn E W.left),
      a.app (op ((Over.post (TopologicalSpace.Opens.map f.base)).obj W))
          (pullLocalSection f E W.left e) =
        b.app (op ((Over.post (TopologicalSpace.Opens.map f.base)).obj W))
          (pullLocalSection f E W.left e)) : a = b := by
  apply (HomConstruction.sectionOverEquiv (pullbackModule f E) H (f ⁻¹ᵁ U)).injective
  apply (localUnitPrecompose_bijective f E H U).injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro e
  exact h W.unop e

theorem localBilinearLift_add {X Y : Scheme} (f : X ⟶ Y)
    {E F G : OModule Y} (b : SheafBilinearMap E F G)
    (U : Y.Opens) (e e' : SectionsOn E U) :
    localBilinearLift f b U (e + e') = localBilinearLift f b U e + localBilinearLift f b U e' := by
  apply localSection_ext f F (pullbackModule f G) U
  intro W z
  change (localBilinearLift f b U (e + e')).app
      (op ((Over.post (TopologicalSpace.Opens.map f.base)).obj W))
      (pullLocalSection f F W.left z) =
    (localBilinearLift f b U e).app
        (op ((Over.post (TopologicalSpace.Opens.map f.base)).obj W))
        (pullLocalSection f F W.left z) +
      (localBilinearLift f b U e').app
        (op ((Over.post (TopologicalSpace.Opens.map f.base)).obj W))
        (pullLocalSection f F W.left z)
  simp only [localBilinearLift_unit, map_add, LinearMap.add_apply, pullLocalSection_add]

theorem localBilinearLift_smul {X Y : Scheme} (f : X ⟶ Y)
    {E F G : OModule Y} (b : SheafBilinearMap E F G)
    (U : Y.Opens) (r : RingSections Y U) (e : SectionsOn E U) :
    localBilinearLift f b U (r • e) = f.app U r • localBilinearLift f b U e := by
  apply localSection_ext f F (pullbackModule f G) U
  intro W z
  change (localBilinearLift f b U (r • e)).app
      (op ((Over.post (TopologicalSpace.Opens.map f.base)).obj W))
      (pullLocalSection f F W.left z) =
    X.presheaf.map ((TopologicalSpace.Opens.map f.base).map W.hom).op (f.app U r) •
      (localBilinearLift f b U e).app
        (op ((Over.post (TopologicalSpace.Opens.map f.base)).obj W))
        (pullLocalSection f F W.left z)
  rw [localBilinearLift_unit, localBilinearLift_unit]
  have hn := congrArg (fun a => a r) (f.naturality W.hom.op)
  change f.app W.left (Y.presheaf.map W.hom.op r) =
    X.presheaf.map ((TopologicalSpace.Opens.map f.base).map W.hom).op (f.app U r) at hn
  let eW : SectionsOn E W.left := E.val.map W.hom.op e
  let rW : RingSections Y W.left := Y.presheaf.map W.hom.op r
  have hr : E.val.map W.hom.op (r • e) =
      @SMul.smul (RingSections Y W.left) (SectionsOn E W.left) inferInstance
        rW eW :=
    Scheme.Modules.map_smul E W.hom r e
  have hs := congrArg (fun e' : SectionsOn E W.left =>
    pullLocalSection f G W.left (b.apply W.left e' z)) hr
  refine hs.trans ?_
  have hb : b.apply W.left (rW • eW) z = rW • b.apply W.left eW z :=
    congrArg (fun q : SectionsOn F W.left →ₗ[RingSections Y W.left]
      SectionsOn G W.left => q z) ((b.apply W.left).map_smul rW eW)
  have hcoeff : f.app W.left rW • pullLocalSection f G W.left (b.apply W.left eW z) =
      X.presheaf.map ((TopologicalSpace.Opens.map f.base).map W.hom).op (f.app U r) •
        pullLocalSection f G W.left (b.apply W.left eW z) :=
    congrArg (fun c : RingSections X (f ⁻¹ᵁ W.left) =>
      c • pullLocalSection f G W.left (b.apply W.left eW z)) hn
  exact (congrArg (pullLocalSection f G W.left) hb).trans
    ((pullLocalSection_smul f G W.left rW (b.apply W.left eW z)).trans hcoeff)

theorem localBilinearLift_restrict {X Y : Scheme} (f : X ⟶ Y)
    {E F G : OModule Y} (b : SheafBilinearMap E F G)
    {U V : Y.Opens} (i : V ⟶ U) (e : SectionsOn E U) :
    localBilinearLift f b V (E.val.map i.op e) =
      HomConstruction.restrictSection ((TopologicalSpace.Opens.map f.base).map i)
        (localBilinearLift f b U e) := by
  apply localSection_ext f F (pullbackModule f G) V
  intro W z
  change (localBilinearLift f b V (E.val.map i.op e)).app
      (op ((Over.post (TopologicalSpace.Opens.map f.base)).obj W))
      (pullLocalSection f F W.left z) =
    (localBilinearLift f b U e).app
      (op ((Over.post (TopologicalSpace.Opens.map f.base)).obj ((Over.map i).obj W)))
      (pullLocalSection f F W.left z)
  have hright : (localBilinearLift f b U e).app
      (op ((Over.post (TopologicalSpace.Opens.map f.base)).obj ((Over.map i).obj W)))
      (pullLocalSection f F W.left z) =
    pullLocalSection f G W.left (b.apply W.left (E.val.map (W.hom ≫ i).op e) z) :=
      localBilinearLift_unit f b U e ((Over.map i).obj W) z
  have hmid :
      pullLocalSection f G W.left
          (b.apply W.left (E.val.map W.hom.op (E.val.map i.op e)) z) =
        pullLocalSection f G W.left
          (b.apply W.left (E.val.map (W.hom ≫ i).op e) z) := by
    apply congrArg (fun e' : SectionsOn E W.left =>
      pullLocalSection f G W.left (b.apply W.left e' z))
    change E.val.map W.hom.op (E.val.map i.op e) = E.val.map (W.hom ≫ i).op e
    rw [op_comp, PresheafOfModules.map_comp_apply]
  exact (localBilinearLift_unit f b V (E.val.map i.op e) W z).trans (hmid.trans hright.symm)

/-- The local lifts form the actual Y-linear adjunct of the desired curry map. -/
def bilinearCurryInput {X Y : Scheme} (f : X ⟶ Y)
    {E F G : OModule Y} (b : SheafBilinearMap E F G) :
    E ⟶ (Scheme.Modules.pushforward f).obj
      (HomConstruction.object (pullbackModule f F) (pullbackModule f G)) where
  val :=
    { app U :=
        ConcreteCategory.ofHom (C := ModuleCat (Y.ringCatSheaf.obj.obj U))
          (X := E.val.obj U)
          (Y := ((Scheme.Modules.pushforward f).obj
            (HomConstruction.object (pullbackModule f F) (pullbackModule f G))).val.obj U)
          { toFun := localBilinearLift f b U.unop
            map_add' := localBilinearLift_add f b U.unop
            map_smul' := localBilinearLift_smul f b U.unop }
      naturality := by
        intro U V i
        ext e
        exact localBilinearLift_restrict f b i.unop e }

def pairing {X Y : Scheme} (f : X ⟶ Y)
    {E F G : OModule Y} (b : SheafBilinearMap E F G) :
    SheafBilinearMap (pullbackModule f E) (pullbackModule f F) (pullbackModule f G) :=
  HomConstruction.bilinearEquiv (pullbackModule f E) (pullbackModule f F) (pullbackModule f G)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv E
      (HomConstruction.object (pullbackModule f F) (pullbackModule f G))).symm
      (bilinearCurryInput f b))

theorem pairing_normalized {X Y : Scheme} (f : X ⟶ Y)
    {E F G : OModule Y} (b : SheafBilinearMap E F G) : IsPullbackPair f b (pairing f b) := by
  intro U e z
  have h := ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv E
    (HomConstruction.object (pullbackModule f F) (pullbackModule f G))).apply_symm_apply
      (bilinearCurryInput f b)
  rw [Adjunction.homEquiv_unit] at h
  have he := congrArg (fun a : E ⟶ (Scheme.Modules.pushforward f).obj
      (HomConstruction.object (pullbackModule f F) (pullbackModule f G)) => a.app U e) h
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    ConcreteCategory.comp_apply] at he
  change HomConstruction.evaluationAt (pullbackModule f F) (pullbackModule f G) (f ⁻¹ᵁ U)
      ((((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv E
        (HomConstruction.object (pullbackModule f F) (pullbackModule f G))).symm
        (bilinearCurryInput f b)).app (f ⁻¹ᵁ U) (pullLocalSection f E U e))
      (pullLocalSection f F U z) = pullLocalSection f G U (b.apply U e z)
  change (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv E
      (HomConstruction.object (pullbackModule f F) (pullbackModule f G))).symm
      (bilinearCurryInput f b)).app (f ⁻¹ᵁ U) (pullLocalSection f E U e) =
    localBilinearLift f b U e at he
  rw [he]
  have hu := localBilinearLift_unit f b U e (Over.mk (𝟙 U)) z
  change (localBilinearLift f b U e).app
      (op (Over.mk ((TopologicalSpace.Opens.map f.base).map (𝟙 U))))
      (pullLocalSection f F U z) =
    pullLocalSection f G U (b.apply U (E.val.map (𝟙 U).op e) z) at hu
  rw [CategoryTheory.Functor.map_id] at hu
  change HomConstruction.evaluationAt (pullbackModule f F) (pullbackModule f G) (f ⁻¹ᵁ U)
      (localBilinearLift f b U e) (pullLocalSection f F U z) =
    pullLocalSection f G U (b.apply U (E.val.map (𝟙 U).op e) z) at hu
  have hid : E.presheaf.map (𝟙 (op U)) e = e :=
    congrArg (fun q : E.presheaf.obj (op U) ⟶ E.presheaf.obj (op U) => q e)
      (CategoryTheory.Functor.map_id E.presheaf (op U))
  exact hu.trans (congrArg (fun x : SectionsOn E U =>
    pullLocalSection f G U (b.apply U x z)) hid)

theorem pairing_unique {X Y : Scheme} (f : X ⟶ Y)
    {E F G : OModule Y} (b : SheafBilinearMap E F G)
    (q : SheafBilinearMap (pullbackModule f E) (pullbackModule f F) (pullbackModule f G))
    (hq : IsPullbackPair f b q) : q = pairing f b := by
  apply (HomConstruction.bilinearEquiv
    (pullbackModule f E) (pullbackModule f F) (pullbackModule f G)).symm.injective
  apply pullbackHom_ext f E
    (HomConstruction.object (pullbackModule f F) (pullbackModule f G))
  intro U e
  apply localSection_ext f F (pullbackModule f G) U
  intro W z
  change q.apply (f ⁻¹ᵁ W.left)
      ((pullbackModule f E).val.map ((TopologicalSpace.Opens.map f.base).map W.hom).op
        (pullLocalSection f E U e)) (pullLocalSection f F W.left z) =
    (pairing f b).apply (f ⁻¹ᵁ W.left)
      ((pullbackModule f E).val.map ((TopologicalSpace.Opens.map f.base).map W.hom).op
        (pullLocalSection f E U e)) (pullLocalSection f F W.left z)
  have hr := pullLocalSection_restrict f E W.hom e
  change (pullbackModule f E).val.map ((TopologicalSpace.Opens.map f.base).map W.hom).op
      (pullLocalSection f E U e) =
    pullLocalSection f E W.left (E.val.map W.hom.op e) at hr
  rw [hr]
  exact (hq W.left (E.val.map W.hom.op e) z).trans
    ((pairing_normalized f b W.left (E.val.map W.hom.op e) z).symm)

/-- The exact original existence-and-uniqueness statement. -/
theorem pullbackPair_existsUnique {X Y : Scheme} (f : X ⟶ Y)
    {E F G : OModule Y} (b : SheafBilinearMap E F G) :
    ∃! q, IsPullbackPair f b q := by
  exact ⟨pairing f b, pairing_normalized f b, fun q hq => pairing_unique f b q hq⟩

end PullbackPairProof

end

theorem pullbackPair_existsUnique {X Y : Scheme} (f : X ⟶ Y)
    {E F G : OModule Y} (b : SheafBilinearMap E F G) :
    ∃! q, IsPullbackPair f b q := by
  exact PullbackPairProof.pullbackPair_existsUnique f b

def pullbackPair {X Y : Scheme} (f : X ⟶ Y)
    {E F G : OModule Y} (b : SheafBilinearMap E F G) :=
  Classical.choose (pullbackPair_existsUnique f b)

theorem pullbackPair_normalized {X Y : Scheme} (f : X ⟶ Y)
    {E F G : OModule Y} (b : SheafBilinearMap E F G) :
    IsPullbackPair f b (pullbackPair f b) :=
  (Classical.choose_spec (pullbackPair_existsUnique f b)).1


end LeBrunSalamon.Skeleton


namespace LeBrunSalamon.Refinement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton

open LeBrunSalamon.PhaseThree

/-- Direction: f*E tensor f*F -> f*(E tensor F). Fixed by the universal
pairing, not by choosing an unspecified isomorphism of equal-rank bundles. -/
def tensorPullbackComparison {Y Z : Scheme} (f : Y ⟶ Z) (E F : OModule Z) :
    tensorSheaf (pullbackModule f E) (pullbackModule f F) ⟶
      pullbackModule f (tensorSheaf E F) :=
  tensorLift (pullbackPair f (tensorPresentation E F).pair)

namespace TensorPullbackComparisonProof

set_option backward.isDefEq.respectTransparency false

open LeBrunSalamon.Skeleton.PullbackPairProof

/-- Unit images in the two arguments determine a pairing into any actual target sheaf. -/
theorem bilinear_pullback_ext {X Y : Scheme} (f : X ⟶ Y)
    {E F : OModule Y} {H : OModule X}
    (q r : SheafBilinearMap (pullbackModule f E) (pullbackModule f F) H)
    (h : ∀ (U : Y.Opens) (e : SectionsOn E U) (z : SectionsOn F U),
      q.apply (f ⁻¹ᵁ U) (pullLocalSection f E U e) (pullLocalSection f F U z) =
        r.apply (f ⁻¹ᵁ U) (pullLocalSection f E U e) (pullLocalSection f F U z)) :
    q = r := by
  apply (HomConstruction.bilinearEquiv
    (pullbackModule f E) (pullbackModule f F) H).symm.injective
  apply pullbackHom_ext f E (HomConstruction.object (pullbackModule f F) H)
  intro U e
  apply localSection_ext f F H U
  intro W z
  change q.apply (f ⁻¹ᵁ W.left)
      ((pullbackModule f E).val.map ((TopologicalSpace.Opens.map f.base).map W.hom).op
        (pullLocalSection f E U e)) (pullLocalSection f F W.left z) =
    r.apply (f ⁻¹ᵁ W.left)
      ((pullbackModule f E).val.map ((TopologicalSpace.Opens.map f.base).map W.hom).op
        (pullLocalSection f E U e)) (pullLocalSection f F W.left z)
  have hr := pullLocalSection_restrict f E W.hom e
  change (pullbackModule f E).val.map ((TopologicalSpace.Opens.map f.base).map W.hom).op
      (pullLocalSection f E U e) =
    pullLocalSection f E W.left (E.val.map W.hom.op e) at hr
  rw [hr]
  exact h W.left (E.val.map W.hom.op e) z

/-- Restrict a pairing to the actual adjunction-unit images and retain its scalar action. -/
def adjointPair {X Y : Scheme} (f : X ⟶ Y)
    {E F : OModule Y} {H : OModule X}
    (b : SheafBilinearMap (pullbackModule f E) (pullbackModule f F) H) :
    SheafBilinearMap E F ((Scheme.Modules.pushforward f).obj H) where
  apply U :=
    { toFun := fun e =>
        { toFun := fun z =>
            b.apply (f ⁻¹ᵁ U) (pullLocalSection f E U e) (pullLocalSection f F U z)
          map_add' := by
            intro z z'
            rw [pullLocalSection_add, map_add]
          map_smul' := by
            intro a z
            change b.apply (f ⁻¹ᵁ U) (pullLocalSection f E U e)
                (pullLocalSection f F U (a • z)) =
              f.app U a • b.apply (f ⁻¹ᵁ U) (pullLocalSection f E U e)
                (pullLocalSection f F U z)
            rw [pullLocalSection_smul, map_smul] }
      map_add' := by
        intro e e'
        apply LinearMap.ext
        intro z
        change b.apply (f ⁻¹ᵁ U) (pullLocalSection f E U (e + e'))
            (pullLocalSection f F U z) =
          b.apply (f ⁻¹ᵁ U) (pullLocalSection f E U e) (pullLocalSection f F U z) +
            b.apply (f ⁻¹ᵁ U) (pullLocalSection f E U e') (pullLocalSection f F U z)
        rw [pullLocalSection_add, map_add, LinearMap.add_apply]
      map_smul' := by
        intro a e
        apply LinearMap.ext
        intro z
        change b.apply (f ⁻¹ᵁ U) (pullLocalSection f E U (a • e))
            (pullLocalSection f F U z) =
          f.app U a • b.apply (f ⁻¹ᵁ U) (pullLocalSection f E U e)
            (pullLocalSection f F U z)
        rw [pullLocalSection_smul, map_smul, LinearMap.smul_apply] }
  naturality := by
    intro U V i e z
    change H.presheaf.map ((TopologicalSpace.Opens.map f.base).map i).op
        (b.apply (f ⁻¹ᵁ V) (pullLocalSection f E V e) (pullLocalSection f F V z)) =
      b.apply (f ⁻¹ᵁ U) (pullLocalSection f E U (E.presheaf.map i.op e))
        (pullLocalSection f F U (F.presheaf.map i.op z))
    rw [b.naturality, pullLocalSection_restrict, pullLocalSection_restrict]

/-- The original comparison acts by the original pullback pairing on every local pure tensor. -/
theorem comparison_pair {Y Z : Scheme} (f : Y ⟶ Z) (E F : OModule Z)
    (U : Y.Opens) (e : SectionsOn (pullbackModule f E) U)
    (z : SectionsOn (pullbackModule f F) U) :
    (tensorPullbackComparison f E F).app U
        ((tensorPresentation (pullbackModule f E) (pullbackModule f F)).pair.apply U e z) =
      (pullbackPair f (tensorPresentation E F).pair).apply U e z := by
  exact congrArg (fun b : SheafBilinearMap (pullbackModule f E)
      (pullbackModule f F) (pullbackModule f (tensorSheaf E F)) => b.apply U e z)
    (tensorLift_pair (pullbackPair f (tensorPresentation E F).pair))

/-- The inverse is the adjoint of the universal pairing on actual pulled-back sections. -/
def inverse {Y Z : Scheme} (f : Y ⟶ Z) (E F : OModule Z) :
    pullbackModule f (tensorSheaf E F) ⟶
      tensorSheaf (pullbackModule f E) (pullbackModule f F) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv
    (tensorSheaf E F) (tensorSheaf (pullbackModule f E) (pullbackModule f F))).symm
    (tensorLift (adjointPair f
      (tensorPresentation (pullbackModule f E) (pullbackModule f F)).pair))

/-- Normalize the inverse on every local unit image, including non-decomposable tensor sections. -/
theorem inverse_unit {Y Z : Scheme} (f : Y ⟶ Z) (E F : OModule Z)
    (U : Z.Opens) (s : SectionsOn (tensorSheaf E F) U) :
    (inverse f E F).app (f ⁻¹ᵁ U) (pullLocalSection f (tensorSheaf E F) U s) =
      (tensorLift (adjointPair f
        (tensorPresentation (pullbackModule f E) (pullbackModule f F)).pair)).app U s := by
  have h := ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv
    (tensorSheaf E F) (tensorSheaf (pullbackModule f E) (pullbackModule f F))).apply_symm_apply
      (tensorLift (adjointPair f
        (tensorPresentation (pullbackModule f E) (pullbackModule f F)).pair))
  rw [Adjunction.homEquiv_unit] at h
  have he := congrArg (fun a : tensorSheaf E F ⟶ (Scheme.Modules.pushforward f).obj
      (tensorSheaf (pullbackModule f E) (pullbackModule f F)) => a.app U s) h
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    ConcreteCategory.comp_apply] at he
  exact he

/-- The inverse sends each pulled-back pure tensor to the pair of its pulled-back factors. -/
theorem inverse_unit_pair {Y Z : Scheme} (f : Y ⟶ Z) (E F : OModule Z)
    (U : Z.Opens) (e : SectionsOn E U) (z : SectionsOn F U) :
    (inverse f E F).app (f ⁻¹ᵁ U)
        (pullLocalSection f (tensorSheaf E F) U ((tensorPresentation E F).pair.apply U e z)) =
      (tensorPresentation (pullbackModule f E) (pullbackModule f F)).pair.apply (f ⁻¹ᵁ U)
        (pullLocalSection f E U e) (pullLocalSection f F U z) := by
  rw [inverse_unit]
  exact congrArg (fun b : SheafBilinearMap E F ((Scheme.Modules.pushforward f).obj
      (tensorSheaf (pullbackModule f E) (pullbackModule f F))) => b.apply U e z)
    (tensorLift_pair (adjointPair f
      (tensorPresentation (pullbackModule f E) (pullbackModule f F)).pair))

theorem comparison_inverse {Y Z : Scheme} (f : Y ⟶ Z) (E F : OModule Z) :
    tensorPullbackComparison f E F ≫ inverse f E F =
      𝟙 (tensorSheaf (pullbackModule f E) (pullbackModule f F)) := by
  apply ((tensorPresentation (pullbackModule f E) (pullbackModule f F)).universal _).1
  apply bilinear_pullback_ext f
  intro U e z
  change (inverse f E F).app (f ⁻¹ᵁ U)
      ((tensorPullbackComparison f E F).app (f ⁻¹ᵁ U)
        ((tensorPresentation (pullbackModule f E) (pullbackModule f F)).pair.apply (f ⁻¹ᵁ U)
          (pullLocalSection f E U e) (pullLocalSection f F U z))) =
    (tensorPresentation (pullbackModule f E) (pullbackModule f F)).pair.apply (f ⁻¹ᵁ U)
      (pullLocalSection f E U e) (pullLocalSection f F U z)
  rw [comparison_pair, pullbackPair_normalized f (tensorPresentation E F).pair U e z,
    inverse_unit_pair]

theorem inverse_comparison {Y Z : Scheme} (f : Y ⟶ Z) (E F : OModule Z) :
    inverse f E F ≫ tensorPullbackComparison f E F =
      𝟙 (pullbackModule f (tensorSheaf E F)) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  have hi : adj.homEquiv (tensorSheaf E F)
      (tensorSheaf (pullbackModule f E) (pullbackModule f F)) (inverse f E F) =
      tensorLift (adjointPair f
        (tensorPresentation (pullbackModule f E) (pullbackModule f F)).pair) :=
    (adj.homEquiv _ _).apply_symm_apply _
  apply (adj.homEquiv (tensorSheaf E F) (pullbackModule f (tensorSheaf E F))).injective
  rw [adj.homEquiv_naturality_right, adj.homEquiv_id, hi]
  apply ((tensorPresentation E F).universal _).1
  apply sheafBilinearMap_ext
  intro U e z
  change (tensorPullbackComparison f E F).app (f ⁻¹ᵁ U)
      ((tensorLift (adjointPair f
        (tensorPresentation (pullbackModule f E) (pullbackModule f F)).pair)).app U
          ((tensorPresentation E F).pair.apply U e z)) =
    pullLocalSection f (tensorSheaf E F) U ((tensorPresentation E F).pair.apply U e z)
  have ht := congrArg (fun b : SheafBilinearMap E F ((Scheme.Modules.pushforward f).obj
      (tensorSheaf (pullbackModule f E) (pullbackModule f F))) => b.apply U e z)
    (tensorLift_pair (adjointPair f
      (tensorPresentation (pullbackModule f E) (pullbackModule f F)).pair))
  change (tensorLift (adjointPair f
      (tensorPresentation (pullbackModule f E) (pullbackModule f F)).pair)).app U
        ((tensorPresentation E F).pair.apply U e z) =
    (tensorPresentation (pullbackModule f E) (pullbackModule f F)).pair.apply (f ⁻¹ᵁ U)
      (pullLocalSection f E U e) (pullLocalSection f F U z) at ht
  rw [ht, comparison_pair]
  exact pullbackPair_normalized f (tensorPresentation E F).pair U e z

end TensorPullbackComparisonProof

theorem tensorPullbackComparison_isIso {Y Z : Scheme} (f : Y ⟶ Z)
    (E F : OModule Z) : IsIso (tensorPullbackComparison f E F) := by
  exact ⟨TensorPullbackComparisonProof.inverse f E F,
    TensorPullbackComparisonProof.comparison_inverse f E F,
    TensorPullbackComparisonProof.inverse_comparison f E F⟩


set_option backward.isDefEq.respectTransparency false in
/-- The tensor pullback normalization on genuine global sections. -/
theorem tensorPullbackComparison_onSections {Y Z : Scheme} (f : Y ⟶ Z)
    {E F : OModule Z} (a : AlgebraicSection E) (b : AlgebraicSection F) :
    tensorSection (pullSection f a) (pullSection f b) ≫
      tensorPullbackComparison f E F = pullSection f (tensorSection a b) := by
  apply (sectionValue_bijective (pullbackModule f (tensorSheaf E F))).injective
  simp only [sectionValue_comp, sectionValue_tensorSection, pullSection_value]
  change (tensorPullbackComparison f E F).app (f ⁻¹ᵁ ⊤)
      ((tensorPresentation (pullbackModule f E) (pullbackModule f F)).pair.apply (f ⁻¹ᵁ ⊤)
        (pullLocalSection f E ⊤ (sectionValue a))
        (pullLocalSection f F ⊤ (sectionValue b))) =
    pullLocalSection f (tensorSheaf E F) ⊤
      ((tensorPresentation E F).pair.apply ⊤ (sectionValue a) (sectionValue b))
  exact (TensorPullbackComparisonProof.comparison_pair f E F (f ⁻¹ᵁ ⊤)
    (pullLocalSection f E ⊤ (sectionValue a))
    (pullLocalSection f F ⊤ (sectionValue b))).trans
      (pullbackPair_normalized f (tensorPresentation E F).pair ⊤
        (sectionValue a) (sectionValue b))



end LeBrunSalamon.Refinement


namespace LeBrunSalamon.Refinement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton

namespace CanonicalPullbackSectionProof

open LeBrunSalamon.PhaseThree

set_option backward.isDefEq.respectTransparency false in
theorem pullbackComp_homEquiv {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    {E : OModule Z} {M : OModule X}
    (h : pullbackModule f (pullbackModule g E) ⟶ M) :
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _
      ((Scheme.Modules.pullbackComp f g).inv.app E ≫ h) =
    (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ h) ≫
        (Scheme.Modules.pushforwardComp f g).hom.app M := by
  let adj := (Scheme.Modules.pullbackPushforwardAdjunction g).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f)
  let adj' := Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)
  have hu := unit_conjugateEquiv adj adj' (Scheme.Modules.pullbackComp f g).inv E
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at hu
  change adj'.homEquiv _ _ ((Scheme.Modules.pullbackComp f g).inv.app E ≫ h) =
    adj.homEquiv _ _ h ≫ (Scheme.Modules.pushforwardComp f g).hom.app M
  rw [adj'.homEquiv_apply, adj.homEquiv_apply, Functor.map_comp,
    ← Category.assoc, ← hu, Category.assoc]
  simpa only [Category.assoc, pullbackModule, Functor.comp_obj, Functor.id_obj] using
    congrArg (fun k => adj.unit.app E ≫ k)
    ((Scheme.Modules.pushforwardComp f g).hom.naturality h).symm

set_option backward.isDefEq.respectTransparency false in
theorem structurePushforwardMap_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    structurePushforwardMap g ≫
      (Scheme.Modules.pushforward g).map (structurePushforwardMap f) ≫
        (Scheme.Modules.pushforwardComp f g).hom.app (structureModule X) =
      structurePushforwardMap (f ≫ g) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext a
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem unitPullbackMap_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Scheme.Modules.pullbackComp f g).inv.app (structureModule Z) ≫
      (Scheme.Modules.pullback f).map (unitPullbackMap g) ≫ unitPullbackMap f =
        unitPullbackMap (f ≫ g) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _).injective
  rw [pullbackComp_homEquiv,
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_left,
    unitPullbackMap_adjoint,
    (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv_naturality_right,
    unitPullbackMap_adjoint, unitPullbackMap_adjoint]
  exact structurePushforwardMap_comp f g

set_option backward.isDefEq.respectTransparency false in
theorem unitPullbackMap_comp_hom {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Scheme.Modules.pullbackComp f g).hom.app (structureModule Z) ≫
      unitPullbackMap (f ≫ g) =
        (Scheme.Modules.pullback f).map (unitPullbackMap g) ≫ unitPullbackMap f := by
  rw [← unitPullbackMap_comp f g]
  simp

set_option backward.isDefEq.respectTransparency false in
theorem unitPullbackIso_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (unitPullbackIso f).inv ≫ (Scheme.Modules.pullback f).map (unitPullbackIso g).inv ≫
      (Scheme.Modules.pullbackComp f g).hom.app (structureModule Z) =
        (unitPullbackIso (f ≫ g)).inv := by
  apply (cancel_mono (unitPullbackIso (f ≫ g)).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id]
  change (unitPullbackIso f).inv ≫ (Scheme.Modules.pullback f).map (unitPullbackIso g).inv ≫
    (Scheme.Modules.pullbackComp f g).hom.app (structureModule Z) ≫
      unitPullbackMap (f ≫ g) = 𝟙 _
  rw [unitPullbackMap_comp_hom]
  change (unitPullbackIso f).inv ≫ (Scheme.Modules.pullback f).map (unitPullbackIso g).inv ≫
    (Scheme.Modules.pullback f).map (unitPullbackIso g).hom ≫ (unitPullbackIso f).hom = 𝟙 _
  simp [← Functor.map_comp_assoc]

set_option backward.isDefEq.respectTransparency false in
theorem pullSection_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    {E : OModule Z} (s : AlgebraicSection E) :
    pullSection f (pullSection g s) ≫ (Scheme.Modules.pullbackComp f g).hom.app E =
      pullSection (f ≫ g) s := by
  have hn := (Scheme.Modules.pullbackComp f g).hom.naturality s
  change (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map s) ≫
      (Scheme.Modules.pullbackComp f g).hom.app E =
    (Scheme.Modules.pullbackComp f g).hom.app (structureModule Z) ≫
      (Scheme.Modules.pullback (f ≫ g)).map s at hn
  simp only [pullSection, restrictSection, Functor.map_comp, Category.assoc]
  rw [hn]
  simpa only [Category.assoc] using
    congrArg (fun k => k ≫ (Scheme.Modules.pullback (f ≫ g)).map s) (unitPullbackIso_comp f g)

end CanonicalPullbackSectionProof

end LeBrunSalamon.Refinement

end
