import RecompileBasePart03

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


namespace LeBrunSalamon.PhaseTwentyFive
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree

namespace HomConstruction.Generic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne

set_option backward.isDefEq.respectTransparency false

variable {C : Type} [Category C] {J : GrothendieckTopology C}

abbrev ringSheaf (R : Sheaf J CommRingCat) : Sheaf J RingCat :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj R

abbrev Modules (R : Sheaf J CommRingCat) := SheafOfModules (ringSheaf R)

abbrev RingSections (R : Sheaf J CommRingCat) (U : C) := ↥(R.obj.obj (op U))

abbrev SectionsOn {R : Sheaf J CommRingCat} (E : Modules R) (U : C) :=
  ↥(E.val.obj (op U))


abbrev restricted {R : Sheaf J CommRingCat} (E : Modules R) (U : C) :=
  (PresheafOfModules.pushforward₀ (Over.forget U) (ringSheaf R).obj).obj E.val

abbrev Section {R : Sheaf J CommRingCat} (E F : Modules R) (U : C) :=
  restricted E U ⟶ restricted F U

abbrev forgetSection {R : Sheaf J CommRingCat} {E F : Modules R} {U : C}
    (φ : Section E F U) : (presheafHom E.val.presheaf F.val.presheaf).obj (op U) :=
  (PresheafOfModules.toPresheaf _).map φ

theorem forgetSection_injective {R : Sheaf J CommRingCat} (E F : Modules R) (U : C) :
    Function.Injective (forgetSection (E := E) (F := F) (U := U)) :=
  (PresheafOfModules.toPresheaf _).map_injective

def smulSection {R : Sheaf J CommRingCat} {E F : Modules R} {U : C}
    (r : RingSections R U) (φ : Section E F U) : Section E F U where
  app V := ModuleCat.ofHom ((R.obj.map V.unop.hom.op r) •
    (show SectionsOn E V.unop.left →ₗ[RingSections R V.unop.left] SectionsOn F V.unop.left
      from (φ.app V).hom))
  naturality := by
    intro V W i
    ext e
    change R.obj.map W.unop.hom.op r • φ.app W (E.val.map i.unop.left.op e) =
      F.val.map i.unop.left.op (R.obj.map V.unop.hom.op r • φ.app V e)
    have hφ := PresheafOfModules.naturality_apply φ i e
    change φ.app W (E.val.map i.unop.left.op e) =
      F.val.map i.unop.left.op (φ.app V e) at hφ
    rw [F.val.map_smul, hφ]
    congr 1
    change R.obj.map W.unop.hom.op r =
      (R.obj.map V.unop.hom.op ≫ R.obj.map i.unop.left.op) r
    rw [← R.obj.map_comp]
    exact congrArg (fun f => R.obj.map f r) (congrArg Quiver.Hom.op (Over.w i.unop).symm)

instance sectionSMul {R : Sheaf J CommRingCat} (E F : Modules R) (U : C) :
    SMul (RingSections R U) (Section E F U) := ⟨smulSection⟩

@[simp] theorem section_smul_app {R : Sheaf J CommRingCat} {E F : Modules R} {U : C}
    (r : RingSections R U) (φ : Section E F U) (V : (Over U)ᵒᵖ)
    (e : E.val.obj (op V.unop.left)) :
    (r • φ).app V e = R.obj.map V.unop.hom.op r • φ.app V e := rfl

instance sectionModule {R : Sheaf J CommRingCat} (E F : Modules R) (U : C) :
    Module (RingSections R U) (Section E F U) where
  one_smul φ := by
    ext V e
    change R.obj.map V.unop.hom.op 1 • φ.app V e = φ.app V e
    simp
  mul_smul a b φ := by
    ext V e
    change R.obj.map V.unop.hom.op (a*b) • φ.app V e =
      R.obj.map V.unop.hom.op a • (R.obj.map V.unop.hom.op b • φ.app V e)
    simp only [map_mul, mul_smul]
  smul_zero a := by
    ext V e
    change R.obj.map V.unop.hom.op a • (0 : SectionsOn F V.unop.left) = 0
    simp
  smul_add a φ ψ := by
    ext V e
    change R.obj.map V.unop.hom.op a • (φ.app V e + ψ.app V e) =
      R.obj.map V.unop.hom.op a • φ.app V e + R.obj.map V.unop.hom.op a • ψ.app V e
    exact smul_add _ _ _
  add_smul a b φ := by
    ext V e
    change R.obj.map V.unop.hom.op (a+b) • φ.app V e =
      R.obj.map V.unop.hom.op a • φ.app V e + R.obj.map V.unop.hom.op b • φ.app V e
    simp only [map_add, add_smul]
  zero_smul φ := by
    ext V e
    change R.obj.map V.unop.hom.op 0 • φ.app V e = 0
    simp



abbrev IsLinear {R : Sheaf J CommRingCat} {E F : Modules R} {U : C}
    (φ : (presheafHom E.val.presheaf F.val.presheaf).obj (op U)) : Prop :=
  ∀ (V : (Over U)ᵒᵖ) (r : RingSections R V.unop.left) (e : SectionsOn E V.unop.left),
    φ.app V (r • e) =
      @SMul.smul (RingSections R V.unop.left) (SectionsOn F V.unop.left) inferInstance r (φ.app V e)

def ofLinear {R : Sheaf J CommRingCat} {E F : Modules R} {U : C}
    (φ : (presheafHom E.val.presheaf F.val.presheaf).obj (op U)) (hφ : IsLinear φ) :
    Section E F U := PresheafOfModules.homMk φ hφ

@[simp] theorem forgetSection_ofLinear {R : Sheaf J CommRingCat} {E F : Modules R} {U : C}
    (φ : (presheafHom E.val.presheaf F.val.presheaf).obj (op U)) (hφ : IsLinear φ) :
    forgetSection (ofLinear φ hφ) = φ := rfl

theorem forgetSection_isLinear {R : Sheaf J CommRingCat} {E F : Modules R} {U : C}
    (φ : Section E F U) : IsLinear (forgetSection φ) := by
  intro V r e
  exact (φ.app V).hom.map_smul r e

def restrictSection {R : Sheaf J CommRingCat} {E F : Modules R} {U V : C}
    (i : V ⟶ U) (φ : Section E F U) : Section E F V :=
  ofLinear ((presheafHom E.val.presheaf F.val.presheaf).map i.op (forgetSection φ))
    (by intro W r e; exact (φ.app (op ((Over.map i).obj W.unop))).hom.map_smul r e)

@[simp] theorem restrictSection_app {R : Sheaf J CommRingCat} {E F : Modules R} {U V : C}
    (i : V ⟶ U) (φ : Section E F U) (W : (Over V)ᵒᵖ) :
    (restrictSection i φ).app W = φ.app (op ((Over.map i).obj W.unop)) := rfl

@[simp] theorem forgetSection_restrict {R : Sheaf J CommRingCat} {E F : Modules R} {U V : C}
    (i : V ⟶ U) (φ : Section E F U) :
    forgetSection (restrictSection i φ) =
      (presheafHom E.val.presheaf F.val.presheaf).map i.op (forgetSection φ) := rfl

@[simp] theorem restrictSection_id {R : Sheaf J CommRingCat} {E F : Modules R} {U : C}
    (φ : Section E F U) : restrictSection (𝟙 U) φ = φ := by
  apply forgetSection_injective
  rw [forgetSection_restrict, op_id, (presheafHom E.val.presheaf F.val.presheaf).map_id]
  rfl

@[simp] theorem restrictSection_comp {R : Sheaf J CommRingCat} {E F : Modules R} {U V W : C}
    (i : V ⟶ U) (j : W ⟶ V) (φ : Section E F U) :
    restrictSection (j ≫ i) φ = restrictSection j (restrictSection i φ) := by
  apply forgetSection_injective
  simp only [forgetSection_restrict, op_comp, CategoryTheory.Functor.map_comp]
  rfl

def restrictAddHom {R : Sheaf J CommRingCat} {E F : Modules R} {U V : C}
    (i : V ⟶ U) : Section E F U →+ Section E F V where
  toFun := restrictSection i
  map_zero' := by ext W e; rfl
  map_add' φ ψ := by ext W e; rfl

def additivePresheaf {R : Sheaf J CommRingCat} (E F : Modules R) : Cᵒᵖ ⥤ AddCommGrpCat where
  obj U := AddCommGrpCat.of (Section E F U.unop)
  map i := AddCommGrpCat.ofHom (restrictAddHom i.unop)
  map_id U := ConcreteCategory.hom_ext _ _ (fun φ => restrictSection_id φ)
  map_comp i j := ConcreteCategory.hom_ext _ _ (fun φ => restrictSection_comp i.unop j.unop φ)

instance additivePresheafModule {R : Sheaf J CommRingCat} (E F : Modules R) (U : Cᵒᵖ) :
    Module ((ringSheaf R).obj.obj U) ((additivePresheaf E F).obj U) :=
  sectionModule E F U.unop

theorem restrictSection_smul {R : Sheaf J CommRingCat} {E F : Modules R} {U V : C}
    (i : V ⟶ U) (r : RingSections R U) (φ : Section E F U) :
    restrictSection i (r • φ) = R.obj.map i.op r • restrictSection i φ := by
  ext W e
  change R.obj.map ((Over.map i).obj W.unop).hom.op r •
      (φ.app (op ((Over.map i).obj W.unop)) e : SectionsOn F W.unop.left) =
    R.obj.map W.unop.hom.op (R.obj.map i.op r) •
      (φ.app (op ((Over.map i).obj W.unop)) e : SectionsOn F W.unop.left)
  congr 1
  change R.obj.map (W.unop.hom ≫ i).op r = _
  rw [op_comp, R.obj.map_comp]
  rfl

def presheaf {R : Sheaf J CommRingCat} (E F : Modules R) : PresheafOfModules (ringSheaf R).obj :=
  PresheafOfModules.ofPresheaf (additivePresheaf E F)
    (by intro U V i r φ; exact restrictSection_smul i.unop r φ)

/-- The linearity predicate on local additive natural transformations. -/
def linearSubfunctor {R : Sheaf J CommRingCat} (E F : Modules R) :
    Subfunctor (presheafHom E.val.presheaf F.val.presheaf) where
  obj U := {φ | IsLinear φ}
  map i φ hφ W r e := hφ (op ((Over.map i.unop).obj W.unop)) r e

def sectionEquiv {R : Sheaf J CommRingCat} (E F : Modules R) (U : C) :
    Section E F U ≃ (linearSubfunctor E F).toFunctor.obj (op U) where
  toFun φ := ⟨forgetSection φ, forgetSection_isLinear φ⟩
  invFun φ := ofLinear φ.val φ.property
  left_inv φ := forgetSection_injective E F U rfl
  right_inv φ := Subtype.ext rfl

def underlyingIso {R : Sheaf J CommRingCat} (E F : Modules R) :
    (presheaf E F).presheaf ⋙ CategoryTheory.forget AddCommGrpCat ≅
      (linearSubfunctor E F).toFunctor :=
  NatIso.ofComponents (fun U => (sectionEquiv E F U.unop).toIso) (by intro U V i; rfl)



lemma linear_at_of_restrict {R : Sheaf J CommRingCat} {E F : Modules R} {U V : C}
    (φ : (presheafHom E.val.presheaf F.val.presheaf).obj (op U)) (i : V ⟶ U)
    (h : IsLinear ((presheafHom E.val.presheaf F.val.presheaf).map i.op φ))
    (r : RingSections R V) (e : SectionsOn E V) :
    φ.app (op (Over.mk i)) (r • e) =
      @SMul.smul (RingSections R V) (SectionsOn F V) inferInstance r
        (φ.app (op (Over.mk i)) e) := by
  have hmap := presheafHom_map_app_op_mk_id (F := E.val.presheaf) (G := F.val.presheaf) i φ
  have hleft := congrArg (fun f => f (r • e)) hmap
  have hright := congrArg (fun f =>
    @SMul.smul (RingSections R V) (SectionsOn F V) inferInstance r (f e)) hmap
  exact hleft.symm.trans ((h (op (Over.mk (𝟙 V))) r e).trans hright)

lemma linearSubfunctor_isSheaf {R : Sheaf J CommRingCat} (E F : Modules R) :
    Presieve.IsSheaf (J)
      (linearSubfunctor E F).toFunctor := by
  have hhom : Presieve.IsSheaf (J)
      (presheafHom E.val.presheaf F.val.presheaf) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp (F.isSheaf.hom E.val.presheaf)
  apply (Subfunctor.isSheaf_iff _ hhom).mpr
  intro U φ hcover V r e
  let S := (linearSubfunctor E F).sieveOfSection φ
  apply F.isSheaf.isSeparated _ (S.pullback V.unop.hom)
    ((J).pullback_stable V.unop.hom hcover)
  intro W g hg
  let f : Over.mk (g ≫ V.unop.hom) ⟶ V.unop := Over.homMk g
  have hn (z : SectionsOn E V.unop.left) :
      φ.app (op (Over.mk (g ≫ V.unop.hom))) (E.val.map g.op z) =
        F.val.map g.op (φ.app V z) := by
    exact congrArg (fun h => h z) (φ.naturality f.op)
  change F.val.map g.op (φ.app V (r • e)) =
    F.val.map g.op (@SMul.smul (RingSections R V.unop.left) (SectionsOn F V.unop.left)
      inferInstance r (φ.app V e))
  have he := E.val.map_smul g.op r e
  have hf := F.val.map_smul g.op r (φ.app V e)
  have hlocal := linear_at_of_restrict φ (g ≫ V.unop.hom) hg
    (R.obj.map g.op r) (E.val.map g.op e)
  exact (hn (r • e)).symm.trans
    ((congrArg (fun z => φ.app (op (Over.mk (g ≫ V.unop.hom))) z) he).trans
      (hlocal.trans ((congrArg (fun z : SectionsOn F W => R.obj.map g.op r • z)
        (hn e)).trans hf.symm)))

/-- The genuine internal-Hom sheaf: local sections are linear morphisms
between the restrictions of the two module sheaves. -/
def object {R : Sheaf J CommRingCat} (E F : Modules R) : Modules R where
  val := presheaf E F
  isSheaf := by
    apply Presheaf.isSheaf_of_isSheaf_comp (J)
      (s := CategoryTheory.forget AddCommGrpCat)
    apply (Presheaf.isSheaf_of_iso_iff (underlyingIso E F)).mpr
    exact (isSheaf_iff_isSheaf_of_type _ _).mpr (linearSubfunctor_isSheaf E F)

end HomConstruction.Generic

namespace HomConstruction.Generic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne

set_option backward.isDefEq.respectTransparency false

variable {C : Type} [Category C] {J : GrothendieckTopology C}


def sectionOverEquiv {R : Sheaf J CommRingCat} (E F : Modules R) (U : C) :
    Section E F U ≃ (E.over U ⟶ F.over U) where
  toFun φ := ⟨φ⟩
  invFun φ :=
    { app V := φ.val.app V
      naturality := by
        intro V W i
        ext e
        exact PresheafOfModules.naturality_apply φ.val i e }
  left_inv φ := by ext V e; rfl
  right_inv φ := by ext V e; rfl

@[simp] theorem sectionOverEquiv_app {R : Sheaf J CommRingCat} (E F : Modules R) (U : C)
    (φ : SectionsOn (object E F) U) (V : (Over U)ᵒᵖ) :
    (sectionOverEquiv E F U φ).val.app V = φ.app V := rfl

theorem sectionOverEquiv_restrict {R : Sheaf J CommRingCat} (E F : Modules R) {U V : C}
    (i : V ⟶ U) (φ : Section E F U) :
    sectionOverEquiv E F V (Generic.restrictSection i φ) =
      (SheafOfModules.overFunctorMap (ringSheaf R) i).inv.app E ≫
        (SheafOfModules.overMap (ringSheaf R) i).map (sectionOverEquiv E F U φ) ≫
          (SheafOfModules.overFunctorMap (ringSheaf R) i).hom.app F := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext e
  rfl

end HomConstruction.Generic

namespace HomConstruction.Generic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne

set_option backward.isDefEq.respectTransparency false

variable {C : Type} [Category C] {J : GrothendieckTopology C}

def iteratedSectionForward {R : Sheaf J CommRingCat} {E F : Modules R}
    {U : C} (V : Over U) (φ : Section E F V.left) :
    Section (R := R.over U) (E.over U) (F.over U) V where
  app W := φ.app (op ((Over.iteratedSliceForward V).obj W.unop))
  naturality := by
    intro W Z i
    ext e
    exact PresheafOfModules.naturality_apply φ ((Over.iteratedSliceForward V).map i.unop).op e

def iteratedSectionBackward {R : Sheaf J CommRingCat} {E F : Modules R}
    {U : C} (V : Over U) (φ : Section (R := R.over U) (E.over U) (F.over U) V) :
    Section E F V.left where
  app W := φ.app (op ((Over.iteratedSliceBackward V).obj W.unop))
  naturality := by
    intro W Z i
    ext e
    exact PresheafOfModules.naturality_apply φ ((Over.iteratedSliceBackward V).map i.unop).op e

lemma iteratedSectionBackward_forward {R : Sheaf J CommRingCat} {E F : Modules R}
    {U : C} (V : Over U) (φ : Section E F V.left) :
    iteratedSectionBackward V (iteratedSectionForward V φ) = φ := by
  apply PresheafOfModules.hom_ext
  intro W
  ext e
  have hh := PresheafOfModules.naturality_apply φ
    ((Over.iteratedSliceEquiv V).counitIso.hom.app W.unop).op e
  change φ.app (op ((Over.iteratedSliceForward V).obj
      ((Over.iteratedSliceBackward V).obj W.unop))) (E.val.map (𝟙 (op W.unop.left)) e) =
    F.val.map (𝟙 (op W.unop.left)) (φ.app W e) at hh
  change φ.app (op ((Over.iteratedSliceForward V).obj
      ((Over.iteratedSliceBackward V).obj W.unop))) e = φ.app W e
  simpa using hh

lemma iteratedSectionForward_backward {R : Sheaf J CommRingCat} {E F : Modules R}
    {U : C} (V : Over U) (φ : Section (R := R.over U) (E.over U) (F.over U) V) :
    iteratedSectionForward V (iteratedSectionBackward V φ) = φ := by
  apply PresheafOfModules.hom_ext
  intro W
  ext e
  have hh := PresheafOfModules.naturality_apply φ
    ((Over.iteratedSliceEquiv V).unitIso.hom.app W.unop).op e
  change φ.app W (E.val.map (𝟙 (op W.unop.left.left)) e) =
    F.val.map (𝟙 (op W.unop.left.left))
      (φ.app (op ((Over.iteratedSliceBackward V).obj
        ((Over.iteratedSliceForward V).obj W.unop))) e) at hh
  change φ.app (op ((Over.iteratedSliceBackward V).obj
      ((Over.iteratedSliceForward V).obj W.unop))) e = φ.app W e
  simpa using hh.symm

local instance iteratedSectionModule {R : Sheaf J CommRingCat} (E F : Modules R)
    {U : C} (V : Over U) :
    Module (RingSections R V.left) (Section (R := R.over U) (E.over U) (F.over U) V) :=
  sectionModule (R := R.over U) (E.over U) (F.over U) V

def iteratedSectionEquiv {R : Sheaf J CommRingCat} (E F : Modules R)
    {U : C} (V : Over U) :
    Section E F V.left ≃ₗ[RingSections R V.left]
      Section (R := R.over U) (E.over U) (F.over U) V where
  toFun := iteratedSectionForward V
  invFun := iteratedSectionBackward V
  left_inv := iteratedSectionBackward_forward V
  right_inv := iteratedSectionForward_backward V
  map_add' φ ψ := by ext W e; rfl
  map_smul' r φ := by ext W e; rfl

/-- Restricting the internal Hom to a slice is the internal Hom of the
restricted sheaves, with the comparison induced by the iterated-slice equivalence. -/
def overIso {R : Sheaf J CommRingCat} (E F : Modules R) (U : C) :
    (object E F).over U ≅ object (R := R.over U) (E.over U) (F.over U) :=
  (SheafOfModules.fullyFaithfulForget ((ringSheaf R).over U)).preimageIso
    (PresheafOfModulesOfCommRing.isoMk (R := (R.over U).obj)
      (M₁ := ((object E F).over U).val)
      (M₂ := (object (R := R.over U) (E.over U) (F.over U)).val)
      (fun V => (iteratedSectionEquiv E F V.unop).toModuleIso)
      (by
        intro V W i
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro φ
        apply PresheafOfModules.hom_ext
        intro Z
        ext e
        rfl))

end HomConstruction.Generic

namespace HomConstruction.Generic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne

set_option backward.isDefEq.respectTransparency false

/-- The ringed-site Hom construction specializes to the concrete scheme
construction used by the tensor-Hom presentation. -/
def schemeIso {X : Scheme} (E F : OModule X) :
    HomConstruction.object E F ≅ object (R := X.sheaf) E F := Iso.refl _

end HomConstruction.Generic


namespace HomConstruction.Generic
set_option backward.isDefEq.respectTransparency false

section

variable {C : Type} [Category C] {J : GrothendieckTopology C}
variable {R : Sheaf J CommRingCat}

def sectionMap {E F E' F' : Modules R} (f : E' ⟶ E) (g : F ⟶ F') (U : C) :
    Section E F U →ₗ[RingSections R U] Section E' F' U where
  toFun φ :=
    (PresheafOfModules.pushforward₀ (Over.forget U) (ringSheaf R).obj).map f.val ≫ φ ≫
      (PresheafOfModules.pushforward₀ (Over.forget U) (ringSheaf R).obj).map g.val
  map_add' φ ψ := by ext V e; simp
  map_smul' r φ := by
    ext V e
    change g.val.app (op V.unop.left)
        ((r • φ).app V (f.val.app (op V.unop.left) e)) =
      R.obj.map V.unop.hom.op r •
        g.val.app (op V.unop.left) (φ.app V (f.val.app (op V.unop.left) e))
    rw [section_smul_app]
    exact (g.val.app (op V.unop.left)).hom.map_smul _ _

/-- The actual Hom sheaf acts contravariantly and covariantly on sheaf maps. -/
def map {E F E' F' : Modules R} (f : E' ⟶ E) (g : F ⟶ F') :
    object E F ⟶ object E' F' where
  val.app U := ModuleCat.ofHom (sectionMap f g U.unop)
  val.naturality := by
    intro U V i
    ext φ W e
    rfl

@[simp] theorem map_app {E F E' F' : Modules R}
    (f : E' ⟶ E) (g : F ⟶ F') (U : Cᵒᵖ) (φ : Section E F U.unop)
    (V : (Over U.unop)ᵒᵖ) (e : E'.val.obj (op V.unop.left)) :
    ((map f g).val.app U φ).app V e =
      g.val.app (op V.unop.left) (φ.app V (f.val.app (op V.unop.left) e)) := rfl

@[simp] theorem map_id (E F : Modules R) : map (𝟙 E) (𝟙 F) = 𝟙 (object E F) := by
  ext U φ V e
  rfl

theorem map_comp {E F E' F' E'' F'' : Modules R}
    (f : E' ⟶ E) (g : F ⟶ F') (f' : E'' ⟶ E') (g' : F' ⟶ F'') :
    map f g ≫ map f' g' = map (f' ≫ f) (g ≫ g') := by
  ext U φ V e
  rfl

def mapIso {E F E' F' : Modules R} (e : E ≅ E') (f : F ≅ F') :
    object E F ≅ object E' F' where
  hom := map e.inv f.hom
  inv := map e.hom f.inv
  hom_inv_id := by rw [map_comp]; simp
  inv_hom_id := by rw [map_comp]; simp

end


section

variable {C : Type} [Category.{0} C] [HasBinaryProducts C]
variable {J : GrothendieckTopology C} {R : Sheaf J CommRingCat}
variable [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U, HasSheafify (J.over U) AddCommGrpCat]
variable [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat]

def freeSectionEquiv (F : Modules R) (I : Type) (U : C) :
    Section (SheafOfModules.free (R := ringSheaf R) I) F U ≃
      (I → SectionsOn F U) :=
  (sectionOverEquiv _ F U).trans (SheafModuleLocal.freeOverHomEquiv F I U)

theorem freeSectionEquiv_apply (F : Modules R) (I : Type) (U : C)
    (φ : Section (SheafOfModules.free (R := ringSheaf R) I) F U) (i : I) :
    freeSectionEquiv F I U φ i =
      φ.app (op (Over.mk (𝟙 U)))
        ((SheafOfModules.freeSection (R := ringSheaf R) i).val (op U)) := by
  exact SheafModuleLocal.freeOverHomEquiv_apply F I U (sectionOverEquiv _ F U φ) i

end


section

variable {C : Type} [Category.{0} C] [HasBinaryProducts C]
variable {J : GrothendieckTopology C} {R : Sheaf J CommRingCat}
variable [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U, HasSheafify (J.over U) AddCommGrpCat]
variable [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat]

/-- Basis coordinates on local Hom sections preserve the local scalar action. -/
def freeSectionLinearEquiv (F : Modules R) (I : Type) (U : C) :
    Section (SheafOfModules.free (R := ringSheaf R) I) F U ≃ₗ[RingSections R U]
      (I → SectionsOn F U) where
  __ := freeSectionEquiv F I U
  map_add' φ ψ := by
    funext i
    change freeSectionEquiv F I U (φ + ψ) i =
      freeSectionEquiv F I U φ i + freeSectionEquiv F I U ψ i
    rw [freeSectionEquiv_apply, freeSectionEquiv_apply, freeSectionEquiv_apply]
    rfl
  map_smul' r φ := by
    funext i
    change freeSectionEquiv F I U (r • φ) i = r • freeSectionEquiv F I U φ i
    rw [freeSectionEquiv_apply, freeSectionEquiv_apply, section_smul_app]
    change R.obj.map (𝟙 U).op r • _ = r • _
    simp

/-- Restriction of a local linear map restricts every one of its basis images. -/
theorem freeSectionEquiv_restrict (F : Modules R) (I : Type) {U V : C}
    (i : V ⟶ U)
    (φ : Section (SheafOfModules.free (R := ringSheaf R) I) F U) :
    freeSectionEquiv F I V (restrictSection i φ) =
      fun a => F.val.map i.op (freeSectionEquiv F I U φ a) := by
  funext a
  rw [freeSectionEquiv_apply, freeSectionEquiv_apply]
  let j : (Over.map i).obj (Over.mk (𝟙 V)) ⟶ Over.mk (𝟙 U) :=
    Over.homMk i (by simp)
  have hn := PresheafOfModules.naturality_apply φ j.op
    ((SheafOfModules.freeSection (R := ringSheaf R) a).val (op U))
  change φ.app (op ((Over.map i).obj (Over.mk (𝟙 V))))
      ((SheafOfModules.free (R := ringSheaf R) I).val.map i.op
        ((SheafOfModules.freeSection (R := ringSheaf R) a).val (op U))) = _ at hn
  have hs : (SheafOfModules.free (R := ringSheaf R) I).val.map i.op
      ((SheafOfModules.freeSection (R := ringSheaf R) a).val (op U)) =
      (SheafOfModules.freeSection (R := ringSheaf R) a).val (op V) :=
    (SheafOfModules.freeSection (R := ringSheaf R) a).property i.op
  rw [hs] at hn
  exact hn

/-- Evaluation of a local linear map at one specified generator. -/
def freeSourceProjection (F : Modules R) (I : Type) (i : I) :
    object (SheafOfModules.free (R := ringSheaf R) I) F ⟶ F where
  val.app U := ModuleCat.ofHom
    ((LinearMap.proj i).comp (freeSectionLinearEquiv F I U.unop).toLinearMap)
  val.naturality := by
    intro U V f
    ext φ
    exact congrFun (freeSectionEquiv_restrict F I f.unop φ) i

/-- A family of sheaf maps uniquely specifies a map into the Hom from a free sheaf. -/
def freeSourceLift {Z F : Modules R} {I : Type} (f : I → (Z ⟶ F)) :
    Z ⟶ object (SheafOfModules.free (R := ringSheaf R) I) F where
  val.app U := ModuleCat.ofHom
    ((freeSectionLinearEquiv F I U.unop).symm.toLinearMap.comp
      (LinearMap.pi (fun i => ((f i).val.app U).hom)))
  val.naturality := by
    intro U V g
    ext z
    apply (freeSectionEquiv F I V.unop).injective
    change freeSectionEquiv F I V.unop
        ((freeSectionEquiv F I V.unop).symm
          (fun i => (f i).val.app V (Z.val.map g z))) =
      freeSectionEquiv F I V.unop
        (restrictSection g.unop ((freeSectionEquiv F I U.unop).symm
          (fun i => (f i).val.app U z)))
    rw [Equiv.apply_symm_apply, freeSectionEquiv_restrict]
    simp only [Equiv.apply_symm_apply]
    funext i
    exact PresheafOfModules.naturality_apply (f i).val g z

@[reassoc (attr := simp)] theorem freeSourceLift_projection
    {Z F : Modules R} {I : Type} (f : I → (Z ⟶ F)) (i : I) :
    freeSourceLift f ≫ freeSourceProjection F I i = f i := by
  ext U z
  exact congrFun ((freeSectionEquiv F I U.unop).apply_symm_apply
    (fun a => (f a).val.app U z)) i

theorem freeSource_hom_ext {Z F : Modules R} {I : Type}
    (f g : Z ⟶ object (SheafOfModules.free (R := ringSheaf R) I) F)
    (h : ∀ i, f ≫ freeSourceProjection F I i = g ≫ freeSourceProjection F I i) :
    f = g := by
  ext U z
  apply (freeSectionEquiv F I U.unop).injective
  funext i
  exact congrArg (fun k : Z ⟶ F => k.val.app U z) (h i)

/-- The actual internal Hom from a free sheaf is the product of its targets. -/
def freeSourceIso (F : Modules R) (I : Type) :
    object (SheafOfModules.free (R := ringSheaf R) I) F ≅ ∏ᶜ (fun _ : I => F) where
  hom := Pi.lift (fun i => freeSourceProjection F I i)
  inv := freeSourceLift (fun i => Pi.π (fun _ : I => F) i)
  hom_inv_id := by
    apply freeSource_hom_ext
    intro i
    rw [Category.assoc, freeSourceLift_projection, Pi.lift_comp_π, Category.id_comp]
  inv_hom_id := by
    apply Pi.hom_ext
    intro i
    rw [Category.assoc, Pi.lift_comp_π, freeSourceLift_projection, Category.id_comp]

end


section

variable {C : Type} [Category.{0} C] [HasBinaryProducts C]
variable {J : GrothendieckTopology C} {R : Sheaf J CommRingCat}
variable [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U, HasSheafify (J.over U) AddCommGrpCat]
variable [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat]

/-- Matrix coordinates identify Hom between free sheaves with a free sheaf. -/
def freeHomIso (I K : Type) [Finite I] :
    object (SheafOfModules.free (R := ringSheaf R) I)
      (SheafOfModules.free (R := ringSheaf R) K) ≅
      SheafOfModules.free (R := ringSheaf R) (Σ _ : I, K) := by
  letI : HasBiproduct (fun _ : I => SheafOfModules.free (R := ringSheaf R) K) :=
    HasBiproduct.of_hasProduct _
  exact freeSourceIso (SheafOfModules.free (R := ringSheaf R) K) I ≪≫
    biproductIso (fun _ : I => SheafOfModules.free (R := ringSheaf R) K) ≪≫
    sigmaSigmaIso (fun _ : I => K) (fun _ _ => SheafOfModules.unit (ringSheaf R))

/-- The dual of the free sheaf has its actual dual basis. -/
def freeDualIso (I : Type) [Finite I] :
    object (SheafOfModules.free (R := ringSheaf R) I)
      (SheafOfModules.unit (ringSheaf R)) ≅ SheafOfModules.free (R := ringSheaf R) I := by
  letI : HasBiproduct (fun _ : I => SheafOfModules.unit (ringSheaf R)) :=
    HasBiproduct.of_hasProduct _
  exact freeSourceIso (SheafOfModules.unit (ringSheaf R)) I ≪≫
    biproductIso (fun _ : I => SheafOfModules.unit (ringSheaf R))

/-- Finite matrix coordinates have precisely the product of the two ranks. -/
def finiteFreeHomIso (r s : ℕ) :
    object (SheafOfModules.free (R := ringSheaf R) (Fin r))
      (SheafOfModules.free (R := ringSheaf R) (Fin s)) ≅
      SheafOfModules.free (R := ringSheaf R) (Fin (r * s)) :=
  freeHomIso (Fin r) (Fin s) ≪≫
    (SheafOfModules.freeFunctor (R := ringSheaf R)).mapIso
      (((Equiv.sigmaEquivProd (Fin r) (Fin s)).trans finProdFinEquiv).toIso)

/-- Transport the matrix coordinates through specified local trivializations. -/
def isoOfFreeTrivializations {E F : Modules R} {r s : ℕ}
    (e : E ≅ SheafOfModules.free (R := ringSheaf R) (Fin r))
    (f : F ≅ SheafOfModules.free (R := ringSheaf R) (Fin s)) :
    object E F ≅ SheafOfModules.free (R := ringSheaf R) (Fin (r * s)) :=
  mapIso e f ≪≫ finiteFreeHomIso r s

end


end HomConstruction.Generic

section
set_option backward.isDefEq.respectTransparency false

/-- The chosen representing object is canonically identified with the
actual sheaf of local module morphisms. -/
def internalHomConstructionIso {X : Scheme} (E F : OModule X) :
    internalHomSheaf E F ≅ HomConstruction.object E F :=
  (internalHomPresentation E F).uniqueIso (HomConstruction.presentation E F)

theorem internalHomConstructionIso_evaluate {X : Scheme} (E F : OModule X) :
    tensorMap (internalHomConstructionIso E F).hom (𝟙 E) ≫
      (HomConstruction.presentation E F).evaluate =
        (internalHomPresentation E F).evaluate :=
  (internalHomPresentation E F).uniqueIso_evaluate (HomConstruction.presentation E F)

/-- Comparison with the ringed-site internal Hom, retaining the original
choice of tensor-Hom presentation. -/
def internalHomGenericIso {X : Scheme} (E F : OModule X) :
    internalHomSheaf E F ≅ HomConstruction.Generic.object (R := X.sheaf) E F :=
  internalHomConstructionIso E F ≪≫ HomConstruction.Generic.schemeIso E F

/-- The chosen internal Hom restricts to the genuine internal Hom on the
slice site. -/
def internalHomOverIso {X : Scheme} (E F : OModule X) (U : X.Opens) :
    (internalHomSheaf E F).over U ≅
      HomConstruction.Generic.object (R := X.sheaf.over U) (E.over U) (F.over U) :=
  (SheafOfModules.overFunctor X.ringCatSheaf U).mapIso (internalHomGenericIso E F) ≪≫
    HomConstruction.Generic.overIso (R := X.sheaf) E F U

end

theorem internalHom_locallyFree {X : Scheme} {E F : OModule X}
    {r s : ℕ} (hE : IsLocallyFreeOfRank E r)
    (hF : IsLocallyFreeOfRank F s) :
    IsLocallyFreeOfRank (internalHomSheaf E F) (r * s) := by
  obtain ⟨ι, U, hU, ⟨eE⟩, ⟨eF⟩⟩ := SheafTensor.exists_common_free_cover hE hF
  apply SheafTensor.rank_of_free_cover (internalHomSheaf E F) (r * s) U hU
  intro i
  exact (HomConstruction.Generic.finiteFreeHomIso (R := X.sheaf.over (U i)) r s).symm ≪≫
    HomConstruction.Generic.mapIso (eE i) (eF i) ≪≫
      (internalHomOverIso E F (U i)).symm

theorem dualSheaf_locallyFree {X : Scheme} {E : OModule X}
    {r : ℕ} (hE : IsLocallyFreeOfRank E r) :
    IsLocallyFreeOfRank (dualSheaf E) r := by
  obtain ⟨q, hq, hr⟩ := hE
  letI := hq
  apply SheafTensor.rank_of_free_cover (dualSheaf E) r q.X q.coversTop
  intro i
  let eO : SheafOfModules.unit (X.ringCatSheaf.over (q.X i)) ≅
      (structureModule X).over (q.X i) := Iso.refl _
  exact (HomConstruction.Generic.freeDualIso (R := X.sheaf.over (q.X i)) (Fin r)).symm ≪≫
    HomConstruction.Generic.mapIso (SheafTensor.localBasisTrivialization q hr i) eO ≪≫
      (internalHomOverIso E (structureModule X) (q.X i)).symm

end LeBrunSalamon.PhaseTwentyFive

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Opposite

namespace LeBrunSalamon.SheafModuleLocal

variable {C : Type} [Category C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat}

/-- A morphism of module sheaves is invertible if it is invertible on a
genuine covering family of slice sites. -/
theorem isIso_of_coversTop {ι : Type} {U : ι → C}
    (hU : J.CoversTop U) {E F : SheafOfModules R} (f : E ⟶ F)
    (h : ∀ i, IsIso (f.over (U i))) : IsIso f := by
  letI : IsIso ((SheafOfModules.toSheaf R).map f) := by
    apply Sheaf.isIso_of_coversTop hU
    intro i
    letI := h i
    change IsIso ((SheafOfModules.toSheaf (R.over (U i))).map (f.over (U i)))
    infer_instance
  exact isIso_of_reflects_iso f (SheafOfModules.toSheaf R)

theorem isIso_iff_of_coversTop {ι : Type} {U : ι → C}
    (hU : J.CoversTop U) {E F : SheafOfModules R} (f : E ⟶ F) :
    IsIso f ↔ ∀ i, IsIso (f.over (U i)) := by
  constructor
  · intro h i
    letI := h
    infer_instance
  · exact isIso_of_coversTop hU f

end LeBrunSalamon.SheafModuleLocal

end

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Opposite

namespace LeBrunSalamon.PhaseTwentyFive.HomConstruction.Generic

variable {C : Type} [Category C] {J : GrothendieckTopology C}
variable {R : Sheaf J CommRingCat}

/-- Evaluation at the terminal object of the local slice. -/
def evaluationAt (E F : Modules R) (U : C) :
    Section E F U →ₗ[RingSections R U]
      (SectionsOn E U →ₗ[RingSections R U] SectionsOn F U) where
  toFun φ := (φ.app (op (Over.mk (𝟙 U)))).hom
  map_add' φ ψ := rfl
  map_smul' r φ := by
    ext e
    change R.obj.map (𝟙 U).op r • φ.app (op (Over.mk (𝟙 U))) e =
      r • φ.app (op (Over.mk (𝟙 U))) e
    simp

theorem evaluationAt_restrict {E F : Modules R} {U V : C}
    (i : V ⟶ U) (φ : Section E F U) (e : SectionsOn E V) :
    evaluationAt E F V (restrictSection i φ) e =
      φ.app (op (Over.mk i)) e := by
  exact congrArg (fun f => f e)
    (presheafHom_map_app_op_mk_id (F := E.val.presheaf) (G := F.val.presheaf) i
      (forgetSection φ))

theorem evaluationAt_naturality {E F : Modules R} {U V : C}
    (i : V ⟶ U) (φ : Section E F U) (e : SectionsOn E U) :
    F.val.map i.op (evaluationAt E F U φ e) =
      evaluationAt E F V (restrictSection i φ) (E.val.map i.op e) := by
  have hh := PresheafOfModules.naturality_apply φ
    (Over.homMk i : Over.mk i ⟶ Over.mk (𝟙 U)).op e
  change φ.app (op (Over.mk i)) (E.val.map i.op e) =
    F.val.map i.op (φ.app (op (Over.mk (𝟙 U))) e) at hh
  exact hh.symm.trans (evaluationAt_restrict i φ (E.val.map i.op e)).symm

abbrev dual (E : Modules R) : Modules R := object E (SheafOfModules.unit (ringSheaf R))

def dualMap {E F : Modules R} (f : E ⟶ F) : dual F ⟶ dual E := map f (𝟙 _)

@[simp] theorem dualMap_id (E : Modules R) : dualMap (𝟙 E) = 𝟙 (dual E) :=
  map_id E _

@[simp] theorem dualMap_comp {E F G : Modules R} (f : E ⟶ F) (g : F ⟶ G) :
    dualMap (f ≫ g) = dualMap g ≫ dualMap f := by
  simp only [dualMap, map_comp, Category.id_comp]

@[simp] theorem dualMap_add {E F : Modules R} (f g : E ⟶ F) :
    dualMap (f + g) = dualMap f + dualMap g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply PresheafOfModules.hom_ext
  intro V
  ext e
  change φ.app V ((f.val.app (op V.unop.left) + g.val.app (op V.unop.left)) e) =
    φ.app V (f.val.app (op V.unop.left) e) + φ.app V (g.val.app (op V.unop.left) e)
  exact (φ.app V).hom.map_add _ _

def doubleDualFunctor : Modules R ⥤ Modules R where
  obj E := dual (dual E)
  map f := dualMap (dualMap f)
  map_id E := by simp
  map_comp f g := by simp

instance doubleDualFunctor_additive : (doubleDualFunctor (R := R)).Additive where
  map_add := by intros; exact (congrArg dualMap (dualMap_add _ _)).trans (dualMap_add _ _)

/-- A local section acts on local linear forms by evaluation on every
smaller object, giving a section of the double dual. -/
def bidualSection (E : Modules R) (U : C) (e : SectionsOn E U) :
    Section (dual E) (SheafOfModules.unit (ringSheaf R)) U where
  app V := ModuleCat.ofHom
    ((evaluationAt E (SheafOfModules.unit (ringSheaf R)) V.unop.left).flip
      (E.val.map V.unop.hom.op e))
  naturality := by
    intro V W i
    ext φ
    change evaluationAt E (SheafOfModules.unit (ringSheaf R)) W.unop.left
        (restrictSection i.unop.left φ) (E.val.map W.unop.hom.op e) =
      (SheafOfModules.unit (ringSheaf R)).val.map i.unop.left.op
        (evaluationAt E (SheafOfModules.unit (ringSheaf R)) V.unop.left φ
          (E.val.map V.unop.hom.op e))
    rw [evaluationAt_naturality]
    congr 1
    exact (E.val.congr_map_apply (show W.unop.hom.op =
      V.unop.hom.op ≫ i.unop.left.op from congrArg Quiver.Hom.op (Over.w i.unop).symm) e).trans
        (E.val.map_comp_apply V.unop.hom.op i.unop.left.op e)

/-- The canonical evaluation map from a sheaf to its double dual. -/
def bidualMap (E : Modules R) : E ⟶ dual (dual E) where
  val := PresheafOfModulesOfCommRing.homMk
    (fun U => ModuleCat.ofHom
      { toFun := bidualSection E U.unop
        map_add' e e' := by
          change bidualSection E U.unop (e + e') =
            bidualSection E U.unop e + bidualSection E U.unop e'
          ext V φ
          change (evaluationAt E (SheafOfModules.unit (ringSheaf R)) V.unop.left φ)
              (E.val.map V.unop.hom.op (e + e')) =
            (evaluationAt E (SheafOfModules.unit (ringSheaf R)) V.unop.left φ)
              (E.val.map V.unop.hom.op e) +
            (evaluationAt E (SheafOfModules.unit (ringSheaf R)) V.unop.left φ)
              (E.val.map V.unop.hom.op e')
          simp
        map_smul' r e := by
          change bidualSection E U.unop (r • e) = smulSection r (bidualSection E U.unop e)
          ext V φ
          change (evaluationAt E (SheafOfModules.unit (ringSheaf R)) V.unop.left φ)
              (E.val.map V.unop.hom.op (r • e)) =
            R.obj.map V.unop.hom.op r •
              (evaluationAt E (SheafOfModules.unit (ringSheaf R)) V.unop.left φ)
                (E.val.map V.unop.hom.op e)
          rw [E.val.map_smul]
          exact (evaluationAt E (SheafOfModules.unit (ringSheaf R)) V.unop.left φ).map_smul _ _ })
    (by
      intro U V i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro e
      apply PresheafOfModules.hom_ext
      intro W
      ext φ
      change evaluationAt E (SheafOfModules.unit (ringSheaf R)) W.unop.left φ
          (E.val.map W.unop.hom.op (E.val.map i e)) =
        evaluationAt E (SheafOfModules.unit (ringSheaf R)) W.unop.left φ
          (E.val.map ((Over.map i.unop).obj W.unop).hom.op e)
      rw [← PresheafOfModules.map_comp_apply]
      rfl)

@[simp] theorem bidualMap_app (E : Modules R) (U : Cᵒᵖ) (e : SectionsOn E U.unop)
    (V : (Over U.unop)ᵒᵖ) (φ : Section E (SheafOfModules.unit (ringSheaf R)) V.unop.left) :
    ((bidualMap E).val.app U e).app V φ =
      φ.app (op (Over.mk (𝟙 V.unop.left))) (E.val.map V.unop.hom.op e) := rfl

theorem bidualMap_naturality {E F : Modules R} (f : E ⟶ F) :
    f ≫ bidualMap F = bidualMap E ≫ (doubleDualFunctor (R := R)).map f := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro e
  apply PresheafOfModules.hom_ext
  intro V
  ext φ
  change φ.app (op (Over.mk (𝟙 V.unop.left)))
      (F.val.map V.unop.hom.op (f.val.app U e)) =
    φ.app (op (Over.mk (𝟙 V.unop.left)))
      (f.val.app (op V.unop.left) (E.val.map V.unop.hom.op e))
  exact congrArg (fun z => φ.app (op (Over.mk (𝟙 V.unop.left))) z)
    (PresheafOfModules.naturality_apply f.val V.unop.hom.op e).symm

def bidualNatTrans : 𝟭 (Modules R) ⟶ doubleDualFunctor where
  app := bidualMap
  naturality := by intro E F f; exact bidualMap_naturality f

end LeBrunSalamon.PhaseTwentyFive.HomConstruction.Generic

end

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Opposite

namespace LeBrunSalamon.PhaseTwentyFive.HomConstruction.Generic

variable {C : Type} [Category C] {J : GrothendieckTopology C}
variable {R : Sheaf J CommRingCat}

def unitSectionEquiv (F : Modules R) (U : C) :
    Section (SheafOfModules.unit (ringSheaf R)) F U ≃ SectionsOn F U :=
  (sectionOverEquiv (SheafOfModules.unit (ringSheaf R)) F U).trans
    (SheafModuleLocal.unitOverHomEquiv F U)

@[simp] theorem unitSectionEquiv_apply (F : Modules R) (U : C)
    (φ : Section (SheafOfModules.unit (ringSheaf R)) F U) :
    unitSectionEquiv F U φ = φ.app (op (Over.mk (𝟙 U))) (1 : RingSections R U) := rfl

def unitSectionLinearEquiv (F : Modules R) (U : C) :
    Section (SheafOfModules.unit (ringSheaf R)) F U ≃ₗ[RingSections R U]
      SectionsOn F U where
  __ := unitSectionEquiv F U
  map_add' φ ψ := rfl
  map_smul' r φ := by
    change (r • φ).app (op (Over.mk (𝟙 U))) (1 : RingSections R U) =
      r • φ.app (op (Over.mk (𝟙 U))) (1 : RingSections R U)
    rw [section_smul_app]
    change R.obj.map (𝟙 U).op r • _ = r • _
    simp

/-- The Hom sheaf from the unit is identified with its target by evaluation at one. -/
def unitSourceIso (F : Modules R) :
    object (SheafOfModules.unit (ringSheaf R)) F ≅ F :=
  (SheafOfModules.fullyFaithfulForget (ringSheaf R)).preimageIso
    (PresheafOfModulesOfCommRing.isoMk (R := R.obj)
      (M₁ := (object (SheafOfModules.unit (ringSheaf R)) F).val) (M₂ := F.val)
      (fun U => (unitSectionLinearEquiv F U.unop).toModuleIso)
      (by
        intro U V i
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro φ
        change evaluationAt (SheafOfModules.unit (ringSheaf R)) F V.unop
            (restrictSection i.unop φ) (1 : RingSections R V.unop) =
          F.val.map i (evaluationAt (SheafOfModules.unit (ringSheaf R)) F U.unop φ
            (1 : RingSections R U.unop))
        have h := evaluationAt_naturality i.unop φ (1 : RingSections R U.unop)
        have h1 : (SheafOfModules.unit (ringSheaf R)).val.map i.unop.op
            (1 : RingSections R U.unop) = (1 : RingSections R V.unop) := by
          exact (R.obj.map i.unop.op).hom.map_one
        exact (congrArg (fun z : RingSections R V.unop =>
          evaluationAt (SheafOfModules.unit (ringSheaf R)) F V.unop
            (restrictSection i.unop φ) z) h1).symm.trans h.symm))

@[simp] theorem unitSourceIso_hom_app (F : Modules R) (U : Cᵒᵖ)
    (φ : Section (SheafOfModules.unit (ringSheaf R)) F U.unop) :
    (unitSourceIso F).hom.val.app U φ =
      φ.app (op (Over.mk (𝟙 U.unop))) (1 : RingSections R U.unop) := rfl

@[simp] theorem unitSourceIso_inv_app (F : Modules R) (U : Cᵒᵖ)
    (e : SectionsOn F U.unop) (V : (Over U.unop)ᵒᵖ) (r : RingSections R V.unop.left) :
    ((unitSourceIso F).inv.val.app U e).app V r =
      @SMul.smul (RingSections R V.unop.left) (SectionsOn F V.unop.left) inferInstance r
        (F.val.map V.unop.hom.op e) := rfl

def unitBidualIso : dual (dual (SheafOfModules.unit (ringSheaf R))) ≅
    SheafOfModules.unit (ringSheaf R) :=
  mapIso (unitSourceIso (SheafOfModules.unit (ringSheaf R))) (Iso.refl _) ≪≫
    unitSourceIso (SheafOfModules.unit (ringSheaf R))

@[reassoc] theorem bidualMap_unit_comp :
    bidualMap (SheafOfModules.unit (ringSheaf R)) ≫ (unitBidualIso (R := R)).hom =
      𝟙 (SheafOfModules.unit (ringSheaf R)) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change ((unitSourceIso (SheafOfModules.unit (ringSheaf R))).inv.val.app U
      (1 : RingSections R U.unop)).app (op (Over.mk (𝟙 U.unop)))
        ((SheafOfModules.unit (ringSheaf R)).val.map (𝟙 U.unop).op r) = r
  rw [unitSourceIso_inv_app]
  simp
  exact @mul_one (RingSections R U.unop) inferInstance r

instance isIso_bidualMap_unit : IsIso (bidualMap (SheafOfModules.unit (ringSheaf R))) := by
  exact IsIso.of_isIso_fac_right (bidualMap_unit_comp (R := R))

end LeBrunSalamon.PhaseTwentyFive.HomConstruction.Generic

end

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor

namespace LeBrunSalamon.PhaseTwentyFive.HomConstruction.Generic

variable {C : Type} [Category C] {J : GrothendieckTopology C}
variable {R : Sheaf J CommRingCat}
variable [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]

/-- Canonical biduality is an isomorphism on finite free sheaves: the
additive double-dual functor preserves their finite coproduct presentation. -/
instance isIso_bidualMap_free (I : Type) [Finite I] :
    IsIso (bidualMap (SheafOfModules.free (R := ringSheaf R) I)) := by
  letI := Fintype.ofFinite I
  let K : Discrete I ⥤ Modules R :=
    Discrete.functor (fun _ : I => SheafOfModules.unit (ringSheaf R))
  letI : ∀ i : Discrete I, IsIso ((whiskerLeft K (bidualNatTrans (R := R))).app i) :=
    fun _ => isIso_bidualMap_unit
  letI : IsIso (whiskerLeft K (bidualNatTrans (R := R))) :=
    NatIso.isIso_of_isIso_app _
  exact isIso_app_coconePt_of_preservesColimit K (bidualNatTrans (R := R))
    (SheafOfModules.freeCofan I) (SheafOfModules.isColimitFreeCofan I)

def freeBidualIso (I : Type) [Finite I] :
    SheafOfModules.free (R := ringSheaf R) I ≅
      dual (dual (SheafOfModules.free (R := ringSheaf R) I)) :=
  asIso (bidualMap (SheafOfModules.free (R := ringSheaf R) I))

/-- Reflexivity is transported through an actual finite free trivialization. -/
theorem isIso_bidualMap_of_free_iso {E : Modules R} {I : Type} [Finite I]
    (e : SheafOfModules.free (R := ringSheaf R) I ≅ E) : IsIso (bidualMap E) :=
  (NatTrans.isIso_app_iff_of_iso (bidualNatTrans (R := R)) e).mp
    (isIso_bidualMap_free I)

end LeBrunSalamon.PhaseTwentyFive.HomConstruction.Generic

end

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Opposite

namespace LeBrunSalamon.PhaseTwentyFive.HomConstruction.Generic

variable {C : Type} [Category C] {J : GrothendieckTopology C}
variable {R : Sheaf J CommRingCat}

def dualOverIso (E : Modules R) (U : C) :
    (dual E).over U ≅ dual (R := R.over U) (E.over U) :=
  overIso E (SheafOfModules.unit (ringSheaf R)) U

/-- The double-dual restriction comparison uses the contravariance of
the local Hom in its first argument. -/
def doubleDualOverIso (E : Modules R) (U : C) :
    (dual (dual E)).over U ≅ dual (R := R.over U) (dual (R := R.over U) (E.over U)) :=
  dualOverIso (dual E) U ≪≫ mapIso (dualOverIso E U) (Iso.refl _)

/-- Canonical bidual evaluation commutes with restriction to every slice. -/
theorem bidualMap_over (E : Modules R) (U : C) :
    (bidualMap E).over U ≫ (doubleDualOverIso E U).hom =
      bidualMap (R := R.over U) (E.over U) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro e
  apply PresheafOfModules.hom_ext
  intro W
  ext φ
  change φ.app (op ((Over.iteratedSliceBackward W.unop.left).obj
      (Over.mk (𝟙 W.unop.left.left)))) (E.val.map W.unop.hom.left.op e) =
    φ.app (op (Over.mk (𝟙 W.unop.left))) (E.val.map W.unop.hom.left.op e)
  have hh := PresheafOfModules.naturality_apply φ
    ((Over.iteratedSliceEquiv W.unop.left).unitIso.hom.app
      (Over.mk (𝟙 W.unop.left))).op (E.val.map W.unop.hom.left.op e)
  change φ.app (op (Over.mk (𝟙 W.unop.left)))
      (E.val.map (𝟙 (op W.unop.left.left)) (E.val.map W.unop.hom.left.op e)) =
    (SheafOfModules.unit (ringSheaf R)).val.map (𝟙 (op W.unop.left.left))
      (φ.app (op ((Over.iteratedSliceBackward W.unop.left).obj
        (Over.mk (𝟙 W.unop.left.left)))) (E.val.map W.unop.hom.left.op e)) at hh
  simpa using hh.symm

theorem isIso_bidualMap_over_iff (E : Modules R) (U : C) :
    IsIso ((bidualMap E).over U) ↔ IsIso (bidualMap (R := R.over U) (E.over U)) := by
  rw [← bidualMap_over]
  exact (isIso_comp_right_iff ((bidualMap E).over U) (doubleDualOverIso E U).hom).symm

end LeBrunSalamon.PhaseTwentyFive.HomConstruction.Generic

end

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne

namespace LeBrunSalamon.PhaseTwentyFive

/-- The comparison from the original chosen Hom computes its evaluation
by applying the corresponding local linear morphism to a section. -/
theorem internalHomGenericIso_evaluate_pair {X : Scheme} (E F : OModule X)
    (U : X.Opens) (φ : SectionsOn (internalHomSheaf E F) U) (e : SectionsOn E U) :
    HomConstruction.Generic.evaluationAt (R := X.sheaf) E F U
        ((internalHomGenericIso E F).hom.app U φ) e =
      (internalHomPresentation E F).evaluate.app U
        ((tensorPresentation (internalHomSheaf E F) E).pair.apply U φ e) := by
  have hp := congrArg (fun b : SheafBilinearMap (HomConstruction.object E F) E F =>
    b.apply U ((internalHomConstructionIso E F).hom.app U φ) e)
      (tensorLift_pair (HomConstruction.evaluatePair E F))
  have h := congrArg (fun f : tensorSheaf (internalHomSheaf E F) E ⟶ F =>
    f.app U ((tensorPresentation (internalHomSheaf E F) E).pair.apply U φ e))
      (internalHomConstructionIso_evaluate E F)
  change (HomConstruction.presentation E F).evaluate.app U
      ((tensorMap (internalHomConstructionIso E F).hom (𝟙 E)).app U
        ((tensorPresentation (internalHomSheaf E F) E).pair.apply U φ e)) = _ at h
  rw [tensorMap_apply] at h
  exact hp.symm.trans h

end LeBrunSalamon.PhaseTwentyFive

end

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne

namespace LeBrunSalamon.PhaseTwentyFive.HomConstruction.Generic

variable {C : Type} [Category C] {J : GrothendieckTopology C}
variable {R : Sheaf J CommRingCat}
variable [∀ U, HasSheafify (J.over U) AddCommGrpCat]
variable [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat]

/-- A finite free covering makes the canonical bidual map invertible. -/
theorem isIso_bidualMap_of_free_cover (E : Modules R) {ι : Type} (U : ι → C)
    (hU : J.CoversTop U) (I : ι → Type) [∀ i, Finite (I i)]
    (e : ∀ i, SheafOfModules.free (R := (ringSheaf R).over (U i)) (I i) ≅ E.over (U i)) :
    IsIso (bidualMap E) := by
  apply SheafModuleLocal.isIso_of_coversTop hU
  intro i
  apply (isIso_bidualMap_over_iff E (U i)).mpr
  exact isIso_bidualMap_of_free_iso (R := R.over (U i)) (E := E.over (U i))
    (I := I i) (e i)

end LeBrunSalamon.PhaseTwentyFive.HomConstruction.Generic

namespace LeBrunSalamon.PhaseTwentyFive

/-- The original chosen double dual is compared with the explicit
double dual of local linear forms. -/
def doubleDualGenericIso {X : Scheme} (E : OModule X) :
    dualSheaf (dualSheaf E) ≅
      HomConstruction.Generic.dual (R := X.sheaf)
        (HomConstruction.Generic.dual (R := X.sheaf) E) :=
  internalHomGenericIso (dualSheaf E) (structureModule X) ≪≫
    HomConstruction.Generic.mapIso (internalHomGenericIso E (structureModule X)) (Iso.refl _)

/-- Canonical bidual evaluation, transported to the original chosen
internal-Hom presentations. -/
def bidualSheaf {X : Scheme} (E : OModule X) : E ⟶ dualSheaf (dualSheaf E) :=
  HomConstruction.Generic.bidualMap (R := X.sheaf) E ≫ (doubleDualGenericIso E).inv

@[reassoc (attr := simp)] theorem bidualSheaf_comparison {X : Scheme} (E : OModule X) :
    bidualSheaf E ≫ (doubleDualGenericIso E).hom =
      HomConstruction.Generic.bidualMap (R := X.sheaf) E := by
  simp [bidualSheaf]

theorem locallyFree_bidualSheaf_isIso {X : Scheme} {E : OModule X} {r : ℕ}
    (hE : IsLocallyFreeOfRank E r) : IsIso (bidualSheaf E) := by
  obtain ⟨q, hq, hr⟩ := hE
  letI := hq
  letI : IsIso (HomConstruction.Generic.bidualMap (R := X.sheaf) E) :=
    HomConstruction.Generic.isIso_bidualMap_of_free_cover E q.X q.coversTop
      (fun _ => Fin r) (fun i => SheafTensor.localBasisTrivialization q hr i)
  dsimp [bidualSheaf]
  infer_instance

end LeBrunSalamon.PhaseTwentyFive

end


namespace LeBrunSalamon.PhaseTwentyFive
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree

set_option backward.isDefEq.respectTransparency false in
theorem locallyFree_doubleDual {X : Scheme} {E : OModule X}
    {r : ℕ} (hE : IsLocallyFreeOfRank E r) :
    Nonempty (dualSheaf (dualSheaf E) ≅ E) := by
  letI := locallyFree_bidualSheaf_isIso hE
  exact ⟨(asIso (bidualSheaf E)).symm⟩

/-- **Published input (exact).** The dual of a finite locally free
module is preserved by arbitrary pullback.  This is the finite-dual/base-
change theorem obtained from the dualizability characterization in Stacks
Project, Section 17.18 (Tag 0FNU), together with preservation of duals by
pullback as a strong symmetric monoidal functor. -/
theorem _root_.LeBrunSalamon.PublishedInputs.SheafFunctoriality.pullback_dual
    {X Y : Scheme} (f : X ⟶ Y) {E : OModule Y} {r : ℕ}
    (hE : IsLocallyFreeOfRank E r) :
    Nonempty (pullbackModule f (dualSheaf E) ≅
      dualSheaf (pullbackModule f E)) := by
  sorry

/-- Project API wrapper for the exact finite-dual base-change input. -/
theorem dualSheaf_pullback {X Y : Scheme} (f : X ⟶ Y)
    {E : OModule Y} {r : ℕ} (hE : IsLocallyFreeOfRank E r) :
    Nonempty (pullbackModule f (dualSheaf E) ≅
      dualSheaf (pullbackModule f E)) :=
  LeBrunSalamon.PublishedInputs.SheafFunctoriality.pullback_dual f hE

/-- Relative derivations are natural additive Leibniz maps on ALL opens, annihilating pullbacks of base
functions. This is the ordinary ringed-space definition; it does not require choosing affine charts. -/
structure RelativeSheafDerivation {X S : Scheme}
    (s : X ⟶ S) (E : OModule X) where
  apply : ∀ U : X.Opens, RingSections X U → SectionsOn E U
  zero : ∀ U, apply U 0 = 0
  add : ∀ U a b, apply U (a + b) = apply U a + apply U b
  leibniz : ∀ U a b,
    apply U (a * b) = a • apply U b + b • apply U a
  naturality : ∀ {U V : X.Opens} (i : U ⟶ V) (a : RingSections X V),
    E.presheaf.map i.op (apply V a) = apply U (X.presheaf.map i.op a)
  killsBase : ∀ (W : S.Opens) (a : RingSections S W),
    apply (s ⁻¹ᵁ W) (s.app W a) = 0

def RelativeSheafDerivation.postcompose {X S : Scheme}
    {s : X ⟶ S} {E F : OModule X}
    (D : RelativeSheafDerivation s E) (h : E ⟶ F) :
    RelativeSheafDerivation s F where
  apply U a := h.app U (D.apply U a)
  zero := by intro U; simp [D.zero]
  add := by intros; simp [D.add]
  leibniz := by intros; simp [D.leibniz]
  naturality := by
    intro U V i a
    rw [sheafHom_naturality, D.naturality]
  killsBase := by intros; simp [D.killsBase]

/-- The universal derivation SPECIFIES Ω¹ uniquely up to a unique
isomorphism compatible with d. The derivative is part of the data. -/
structure CotangentPresentation {X S : Scheme} (s : X ⟶ S) where
  object : OModule X
  differential : RelativeSheafDerivation s object
  universal : ∀ E : OModule X,
    Function.Bijective (fun h : object ⟶ E =>
      differential.postcompose h)

/-- **Published input (exact).** Existence of the relative sheaf of
differentials together with its universal derivation.  The structure
`CotangentPresentation` is precisely the representability statement of
Stacks Project, Definition 29.33.1 and Lemma 29.33.2 (Section 29.33,
Tag 01UM), expressed using the preceding definition of relative sheaf
derivations. -/
theorem _root_.LeBrunSalamon.PublishedInputs.SheafFunctoriality.cotangentPresentation
    {X S : Scheme} (s : X ⟶ S) : Nonempty (CotangentPresentation s) := by
  sorry

/-- Project API wrapper for the exact universal-differentials input. -/
theorem cotangentPresentation_exists {X S : Scheme} (s : X ⟶ S) :
    Nonempty (CotangentPresentation s) :=
  LeBrunSalamon.PublishedInputs.SheafFunctoriality.cotangentPresentation s

def cotangentPresentation {X S : Scheme} (s : X ⟶ S) :
    CotangentPresentation s :=
  Classical.choice (cotangentPresentation_exists s)

abbrev cotangentSheaf {X S : Scheme} (s : X ⟶ S) : OModule X :=
  (cotangentPresentation s).object

abbrev tangentSheaf {X S : Scheme} (s : X ⟶ S) : OModule X :=
  dualSheaf (cotangentSheaf s)

def differentialLift {X S : Scheme} {s : X ⟶ S} {E : OModule X}
    (D : RelativeSheafDerivation s E) : cotangentSheaf s ⟶ E :=
  (Equiv.ofBijective
    (fun h : cotangentSheaf s ⟶ E =>
      (cotangentPresentation s).differential.postcompose h)
    ((cotangentPresentation s).universal E)).symm D

theorem differentialLift_spec {X S : Scheme} {s : X ⟶ S}
    {E : OModule X} (D : RelativeSheafDerivation s E) :
    (cotangentPresentation s).differential.postcompose
      (differentialLift D) = D := by
  exact (Equiv.ofBijective _ ((cotangentPresentation s).universal E)).apply_symm_apply D

section CotangentUniquenessProofSection

set_option backward.isDefEq.respectTransparency false

namespace CotangentUniquenessProof

theorem postcompose_id {X S : Scheme} {s : X ⟶ S} {E : OModule X}
    (D : RelativeSheafDerivation s E) : D.postcompose (𝟙 E) = D := by
  cases D
  rfl

theorem postcompose_comp {X S : Scheme} {s : X ⟶ S} {E F G : OModule X}
    (D : RelativeSheafDerivation s E) (f : E ⟶ F) (g : F ⟶ G) :
    D.postcompose (f ≫ g) = (D.postcompose f).postcompose g := by
  rfl

end CotangentUniquenessProof

end CotangentUniquenessProofSection

theorem cotangentPresentation_unique {X S : Scheme} {s : X ⟶ S}
    (P Q : CotangentPresentation s) :
    ∃ e : P.object ≅ Q.object,
      P.differential.postcompose e.hom = Q.differential := by
  set_option backward.isDefEq.respectTransparency false in
    obtain ⟨f, hf⟩ := (P.universal Q.object).2 Q.differential
    obtain ⟨g, hg⟩ := (Q.universal P.object).2 P.differential
    change P.differential.postcompose f = Q.differential at hf
    change Q.differential.postcompose g = P.differential at hg
    refine ⟨{ hom := f, inv := g, hom_inv_id := ?_, inv_hom_id := ?_ }, hf⟩
    · apply (P.universal P.object).1
      change P.differential.postcompose (f ≫ g) = P.differential.postcompose (𝟙 P.object)
      rw [CotangentUniquenessProof.postcompose_comp, hf, hg,
        CotangentUniquenessProof.postcompose_id]
    · apply (Q.universal Q.object).1
      change Q.differential.postcompose (g ≫ f) = Q.differential.postcompose (𝟙 Q.object)
      rw [CotangentUniquenessProof.postcompose_comp, hg, hf,
        CotangentUniquenessProof.postcompose_id]

theorem differentialLift_unique {X S : Scheme} {s : X ⟶ S}
    {E : OModule X} (D : RelativeSheafDerivation s E)
    (h : cotangentSheaf s ⟶ E)
    (hh : (cotangentPresentation s).differential.postcompose h = D) :
    h = differentialLift D := by
  apply ((cotangentPresentation s).universal E).1
  exact hh.trans (differentialLift_spec D).symm

end LeBrunSalamon.PhaseTwentyFive

/- Stacks Project Tags 02G1 and 02G2: the universal differential sheaf of a
smooth morphism is finite locally free of the relative dimension. The
chosen project presentation is compared using its proved universal property. -/
section SmoothCotangentRankProofSection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive

namespace LeBrunSalamon.PublishedInputs.Differentials

/-- The universal differential of a smooth morphism of relative dimension d
is finite locally free of rank d (Stacks 02G1, 02G2). The presentation is
provided as data; comparison with the project's chosen presentation is proved. -/
theorem smoothCotangentPresentation {X S : Scheme} (s : X ⟶ S) (d : ℕ)
    (hs : SmoothOfRelativeDimension d s) :
    ∃ P : CotangentPresentation s, IsLocallyFreeOfRank P.object d := by
  sorry

end LeBrunSalamon.PublishedInputs.Differentials

namespace LeBrunSalamon.CotangentRankProof

theorem rank_transport {X : Scheme} {E F : OModule X} {r : ℕ}
    (e : E ≅ F) (hE : IsLocallyFreeOfRank E r) :
    IsLocallyFreeOfRank F r := by
  obtain ⟨q, hq, hr⟩ := hE
  letI := hq
  apply SheafTensor.rank_of_free_cover F r q.X q.coversTop
  intro i
  exact SheafTensor.localBasisTrivialization q hr i ≪≫
    (SheafOfModules.overFunctor X.ringCatSheaf (q.X i)).mapIso e

theorem smooth_cotangent_rank {X S : Scheme} (s : X ⟶ S) (d : ℕ)
    (hs : SmoothOfRelativeDimension d s) :
    IsLocallyFreeOfRank (cotangentSheaf s) d := by
  obtain ⟨P, hP⟩ := PublishedInputs.Differentials.smoothCotangentPresentation s d hs
  obtain ⟨e, _⟩ := cotangentPresentation_unique P (cotangentPresentation s)
  exact rank_transport e hP

end LeBrunSalamon.CotangentRankProof

end SmoothCotangentRankProofSection

namespace LeBrunSalamon.PhaseTwentyFive
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree

theorem _root_.LeBrunSalamon.PublishedInputs.Step3e.smooth_cotangent_rank
    {X S : Scheme} (s : X ⟶ S) (d : ℕ)
    (hs : SmoothOfRelativeDimension d s) :
    IsLocallyFreeOfRank (cotangentSheaf s) d := by
  exact LeBrunSalamon.CotangentRankProof.smooth_cotangent_rank s d hs

/-- Project-facing form of local freeness of relative differentials for a
smooth morphism of relative dimension `d`. -/
theorem smooth_cotangent_rank {X S : Scheme} (s : X ⟶ S)
    (d : ℕ) (hs : SmoothOfRelativeDimension d s) :
    IsLocallyFreeOfRank (cotangentSheaf s) d := by
  exact LeBrunSalamon.PublishedInputs.Step3e.smooth_cotangent_rank s d hs

theorem smooth_tangent_rank {X S : Scheme} (s : X ⟶ S)
    (d : ℕ) (hs : SmoothOfRelativeDimension d s) :
    IsLocallyFreeOfRank (tangentSheaf s) d :=
  LeBrunSalamon.PhaseTwentyFive.dualSheaf_locallyFree
    (LeBrunSalamon.PhaseTwentyFive.smooth_cotangent_rank s d hs)

/-- The tangent bundle now refers to the universal relative cotangent
sheaf, rather than to an arbitrary input with the expected rank. -/
def intrinsicTangentBundle {d : ℕ} (X : SmoothProperComplexVariety d) :
    AlgebraicVectorBundle X.scheme d :=
  ⟨tangentSheaf X.structureMap,
    smooth_tangent_rank X.structureMap d X.smooth⟩

def intrinsicCotangentBundle {d : ℕ} (X : SmoothProperComplexVariety d) :
    AlgebraicVectorBundle X.scheme d :=
  ⟨cotangentSheaf X.structureMap,
    smooth_cotangent_rank X.structureMap d X.smooth⟩

/-- Evaluation of a dual section on a cotangent section. -/
def tangentCotangentPair {X S : Scheme} (s : X ⟶ S) :
    SheafBilinearMap (tangentSheaf s) (cotangentSheaf s)
      (structureModule X) :=
  (tensorPresentation (tangentSheaf s) (cotangentSheaf s)).pair.postcompose
    (internalHomPresentation (cotangentSheaf s) (structureModule X)).evaluate

/-- A tangent section acts on a regular function by pairing with df.
This fixes the action intrinsically, including its sign convention. -/
def tangentActs {X S : Scheme} (s : X ⟶ S) (U : X.Opens)
    (v : SectionsOn (tangentSheaf s) U) (a : RingSections X U) :
    RingSections X U :=
  (tangentCotangentPair s).apply U v
    ((cotangentPresentation s).differential.apply U a)

noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive

namespace TangentActionProof

theorem zero_field {X S : Scheme} (s : X ⟶ S)
    (U : X.Opens) (a : RingSections X U) : tangentActs s U 0 a = 0 := by
  simp [tangentActs]

theorem zero_function {X S : Scheme} (s : X ⟶ S)
    (U : X.Opens) (v : SectionsOn (tangentSheaf s) U) : tangentActs s U v 0 = 0 := by
  simp [tangentActs, (cotangentPresentation s).differential.zero]

theorem add_field {X S : Scheme} (s : X ⟶ S)
    (U : X.Opens) (v w : SectionsOn (tangentSheaf s) U) (a : RingSections X U) :
    tangentActs s U (v + w) a = tangentActs s U v a + tangentActs s U w a := by
  simp [tangentActs]

theorem add_function {X S : Scheme} (s : X ⟶ S)
    (U : X.Opens) (v : SectionsOn (tangentSheaf s) U) (a b : RingSections X U) :
    tangentActs s U v (a + b) = tangentActs s U v a + tangentActs s U v b := by
  simp [tangentActs, (cotangentPresentation s).differential.add]

def functionAddHom {X S : Scheme} (s : X ⟶ S)
    (U : X.Opens) (v : SectionsOn (tangentSheaf s) U) :
    RingSections X U →+ RingSections X U where
  toFun := tangentActs s U v
  map_zero' := zero_function s U v
  map_add' := add_function s U v

theorem neg_function {X S : Scheme} (s : X ⟶ S)
    (U : X.Opens) (v : SectionsOn (tangentSheaf s) U) (a : RingSections X U) :
    tangentActs s U v (-a) = -tangentActs s U v a :=
  (functionAddHom s U v).map_neg a

theorem sub_function {X S : Scheme} (s : X ⟶ S)
    (U : X.Opens) (v : SectionsOn (tangentSheaf s) U) (a b : RingSections X U) :
    tangentActs s U v (a - b) = tangentActs s U v a - tangentActs s U v b :=
  (functionAddHom s U v).map_sub a b

theorem neg_field {X S : Scheme} (s : X ⟶ S)
    (U : X.Opens) (v : SectionsOn (tangentSheaf s) U) (a : RingSections X U) :
    tangentActs s U (-v) a = -tangentActs s U v a := by
  simp [tangentActs]

theorem sub_field {X S : Scheme} (s : X ⟶ S)
    (U : X.Opens) (v w : SectionsOn (tangentSheaf s) U) (a : RingSections X U) :
    tangentActs s U (v - w) a = tangentActs s U v a - tangentActs s U w a := by
  simp [tangentActs]

theorem smul_field {X S : Scheme} (s : X ⟶ S)
    (U : X.Opens) (v : SectionsOn (tangentSheaf s) U) (a b : RingSections X U) :
    tangentActs s U (a • v) b = a * tangentActs s U v b := by
  simp [tangentActs]

theorem leibniz {X S : Scheme} (s : X ⟶ S)
    (U : X.Opens) (v : SectionsOn (tangentSheaf s) U) (a b : RingSections X U) :
    tangentActs s U v (a * b) =
      a * tangentActs s U v b + b * tangentActs s U v a := by
  simp [tangentActs, (cotangentPresentation s).differential.leibniz]

theorem naturality {X S : Scheme} (s : X ⟶ S)
    {U V : X.Opens} (i : U ⟶ V)
    (v : SectionsOn (tangentSheaf s) V) (a : RingSections X V) :
    X.presheaf.map i.op (tangentActs s V v a) =
      tangentActs s U ((tangentSheaf s).presheaf.map i.op v)
        (X.presheaf.map i.op a) := by
  change (structureModule X).presheaf.map i.op
      ((tangentCotangentPair s).apply V v ((cotangentPresentation s).differential.apply V a)) = _
  rw [(tangentCotangentPair s).naturality,
    (cotangentPresentation s).differential.naturality]
  rfl

theorem killsBase {X S : Scheme} (s : X ⟶ S)
    (W : S.Opens) (v : SectionsOn (tangentSheaf s) (s ⁻¹ᵁ W))
    (a : RingSections S W) : tangentActs s (s ⁻¹ᵁ W) v (s.app W a) = 0 := by
  simp [tangentActs, (cotangentPresentation s).differential.killsBase]

end TangentActionProof

end

theorem tangentActs_leibniz {X S : Scheme} (s : X ⟶ S)
    (U : X.Opens) (v : SectionsOn (tangentSheaf s) U)
    (a b : RingSections X U) :
    tangentActs s U v (a * b) =
      a * tangentActs s U v b + b * tangentActs s U v a := by
  exact TangentActionProof.leibniz s U v a b

section TangentFaithfulnessProofSection

set_option backward.isDefEq.respectTransparency false

namespace TangentFaithfulnessProof

private theorem relativeDerivation_ext {X S : Scheme} {s : X ⟶ S}
    {E : OModule X} {D₁ D₂ : RelativeSheafDerivation s E}
    (h : ∀ U a, D₁.apply U a = D₂.apply U a) : D₁ = D₂ := by
  cases D₁ with
  | mk d₁ z₁ a₁ l₁ n₁ b₁ =>
    cases D₂ with
    | mk d₂ z₂ a₂ l₂ n₂ b₂ =>
      have hd : d₁ = d₂ := funext (fun U => funext (fun a => h U a))
      subst d₂
      rfl

/-- The right adjoint to restriction to the site over the actual open `U`. -/
private abbrev restrictionPushforward {X : Scheme} (E : OModule X) (U : X.Opens) :
    OModule X :=
  (SheafOfModules.pushforward
    (SheafOfModules.pushforwardOver (R := X.ringCatSheaf) U)).obj (E.over U)

private def localHomAdjunct {X : Scheme} {M E : OModule X} {U : X.Opens}
    (φ : M.over U ⟶ E.over U) : M ⟶ restrictionPushforward E U :=
  (SheafOfModules.overPushforwardOverAdj (R := X.ringCatSheaf) U).homEquiv
    M (E.over U) φ

/-- The unit of the over-site adjunction is restriction along its counit.
On opens this is restriction from `V` to `U ∩ V`. -/
private theorem localHomAdjunct_apply {X : Scheme} {M E : OModule X} {U : X.Opens}
    (φ : M.over U ⟶ E.over U) (V : X.Opens) (e : SectionsOn M V) :
    (localHomAdjunct (M := M) (E := E) (U := U) φ).app V e =
      φ.val.app (op ((Over.star U).obj V))
        (M.val.map ((Over.forgetAdjStar U).counit.app V).op e) := by
  rfl

/-- Universality of the actual differential also determines maps on every
restricted site.  The proof uses a genuine right-adjoint target module. -/
theorem restrictedCotangentHom_ext {X S : Scheme} {s : X ⟶ S}
    (P : CotangentPresentation s) (E : OModule X) (U : X.Opens)
    (φ ψ : P.object.over U ⟶ E.over U)
    (h : ∀ (W : Over U) (a : RingSections X W.left),
      φ.val.app (op W) (P.differential.apply W.left a) =
        ψ.val.app (op W) (P.differential.apply W.left a)) : φ = ψ := by
  apply ((SheafOfModules.overPushforwardOverAdj (R := X.ringCatSheaf) U).homEquiv
    P.object (E.over U)).injective
  apply (P.universal (restrictionPushforward E U)).1
  apply relativeDerivation_ext
  intro V a
  change (localHomAdjunct (M := P.object) (E := E) (U := U) φ).app V
      (P.differential.apply V a) =
    (localHomAdjunct (M := P.object) (E := E) (U := U) ψ).app V
      (P.differential.apply V a)
  rw [localHomAdjunct_apply, localHomAdjunct_apply]
  have hd := P.differential.naturality ((Over.forgetAdjStar U).counit.app V) a
  change P.object.val.map ((Over.forgetAdjStar U).counit.app V).op
      (P.differential.apply V a) =
    P.differential.apply ((Over.star U).obj V).left
      (X.presheaf.map ((Over.forgetAdjStar U).counit.app V).op a) at hd
  rw [hd]
  exact h ((Over.star U).obj V)
    (X.presheaf.map ((Over.forgetAdjStar U).counit.app V).op a)

/-- The original dual section, interpreted as an actual local module map. -/
private def localFunctional {X S : Scheme} (s : X ⟶ S) (U : X.Opens)
    (v : SectionsOn (tangentSheaf s) U) :
    (cotangentSheaf s).over U ⟶ (structureModule X).over U :=
  HomConstruction.Generic.sectionOverEquiv (R := X.sheaf)
    (cotangentSheaf s) (structureModule X) U
    ((internalHomGenericIso (cotangentSheaf s) (structureModule X)).hom.app U v)

/-- This is evaluation on the stored differential, with its original
normalization; an arbitrary isomorphism of cotangent objects would not suffice. -/
private theorem localFunctional_apply {X S : Scheme} (s : X ⟶ S) (U : X.Opens)
    (v : SectionsOn (tangentSheaf s) U) (W : Over U) (a : RingSections X W.left) :
    (localFunctional s U v).val.app (op W)
        ((cotangentPresentation s).differential.apply W.left a) =
      tangentActs s W.left ((tangentSheaf s).presheaf.map W.hom.op v) a := by
  let e := internalHomGenericIso (cotangentSheaf s) (structureModule X)
  have hn := sheafHom_naturality e.hom W.hom v
  change HomConstruction.Generic.restrictSection W.hom (e.hom.app U v) =
    e.hom.app W.left ((tangentSheaf s).presheaf.map W.hom.op v) at hn
  calc
    _ = HomConstruction.Generic.evaluationAt (R := X.sheaf) (cotangentSheaf s) (structureModule X)
        W.left (HomConstruction.Generic.restrictSection W.hom (e.hom.app U v))
        ((cotangentPresentation s).differential.apply W.left a) := by
      exact (HomConstruction.Generic.evaluationAt_restrict (R := X.sheaf) W.hom (e.hom.app U v)
        ((cotangentPresentation s).differential.apply W.left a)).symm
    _ = HomConstruction.Generic.evaluationAt (R := X.sheaf) (cotangentSheaf s) (structureModule X)
        W.left (e.hom.app W.left ((tangentSheaf s).presheaf.map W.hom.op v))
        ((cotangentPresentation s).differential.apply W.left a) := by rw [hn]
    _ = _ := internalHomGenericIso_evaluate_pair (cotangentSheaf s) (structureModule X)
      W.left ((tangentSheaf s).presheaf.map W.hom.op v)
      ((cotangentPresentation s).differential.apply W.left a)

end TangentFaithfulnessProof

open TangentFaithfulnessProof in
theorem tangentActs_faithful {X S : Scheme} (s : X ⟶ S)
    (U : X.Opens) (v w : SectionsOn (tangentSheaf s) U)
    (h : ∀ (V : X.Opens) (i : V ⟶ U) (a : RingSections X V),
      tangentActs s V ((tangentSheaf s).presheaf.map i.op v) a =
        tangentActs s V ((tangentSheaf s).presheaf.map i.op w) a) :
    v = w := by
  let e := internalHomGenericIso (cotangentSheaf s) (structureModule X)
  have hlocal : localFunctional s U v = localFunctional s U w := by
    apply restrictedCotangentHom_ext (cotangentPresentation s) (structureModule X) U
    intro W a
    rw [localFunctional_apply, localFunctional_apply]
    exact h W.left W.hom a
  change HomConstruction.Generic.sectionOverEquiv (R := X.sheaf)
      (cotangentSheaf s) (structureModule X) U
      (e.hom.app U v) =
    HomConstruction.Generic.sectionOverEquiv (R := X.sheaf)
      (cotangentSheaf s) (structureModule X) U
      (e.hom.app U w) at hlocal
  have heq : e.hom.app U v = e.hom.app U w :=
    (HomConstruction.Generic.sectionOverEquiv (R := X.sheaf)
      (cotangentSheaf s) (structureModule X) U).injective hlocal
  have hinv (z : SectionsOn (tangentSheaf s) U) :
      e.inv.app U (e.hom.app U z) = z := by
    change (e.hom ≫ e.inv).app U z = z
    rw [e.hom_inv_id]
    rfl
  exact (hinv v).symm.trans ((congrArg (fun z => e.inv.app U z) heq).trans (hinv w))

end TangentFaithfulnessProofSection

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseThree

namespace LocalDerivationProof

/-- A relative derivation on all objects of the actual site over an open.
The base-annihilation law includes all restrictions of base functions. -/
structure LocalDerivation {X S : Scheme} (s : X ⟶ S)
    (E : OModule X) (U : X.Opens) where
  apply : ∀ W : Over U, RingSections X W.left → SectionsOn E W.left
  zero : ∀ W, apply W 0 = 0
  add : ∀ W a b, apply W (a + b) = apply W a + apply W b
  leibniz : ∀ W a b, apply W (a * b) = a • apply W b + b • apply W a
  naturality : ∀ {V W : Over U} (i : V ⟶ W) (a : RingSections X W.left),
    E.presheaf.map i.left.op (apply W a) = apply V (X.presheaf.map i.left.op a)
  killsBase : ∀ (V : S.Opens) (a : RingSections S V)
    (W : Over U) (i : W.left ⟶ s ⁻¹ᵁ V),
    apply W (X.presheaf.map i.op (s.app V a)) = 0

/-- The existing right adjoint to restriction, with no new sheaf construction. -/
abbrev restrictionPushforward {X : Scheme} (E : OModule X) (U : X.Opens) :
    OModule X :=
  (SheafOfModules.pushforward
    (SheafOfModules.pushforwardOver (R := X.ringCatSheaf) U)).obj (E.over U)

theorem ringRestrict_comp {X : Scheme} {U V W : X.Opens}
    (i : U ⟶ V) (j : V ⟶ W) (a : RingSections X W) :
    X.presheaf.map i.op (X.presheaf.map j.op a) =
      X.presheaf.map (i ≫ j).op a := by
  simp only [op_comp, Functor.map_comp, CommRingCat.comp_apply]

theorem moduleRestrict_comp {X : Scheme} (E : OModule X)
    {U V W : X.Opens} (i : U ⟶ V) (j : V ⟶ W) (e : SectionsOn E W) :
    E.presheaf.map i.op (E.presheaf.map j.op e) =
      E.presheaf.map (i ≫ j).op e := by
  change E.val.map i.op (E.val.map j.op e) = E.val.map (i ≫ j).op e
  rw [op_comp, PresheafOfModules.map_comp_apply]

/-- The scalar action on the right-adjoint target is the actual restriction
of scalars along the counit, rather than a separately chosen module action. -/
theorem restrictionPushforward_smul {X : Scheme} (E : OModule X)
    (U V : X.Opens) (a : RingSections X V)
    (e : SectionsOn E ((Over.star U).obj V).left) :
    @SMul.smul (RingSections X V) (SectionsOn (restrictionPushforward E U) V)
        inferInstance a e =
      @SMul.smul (RingSections X ((Over.star U).obj V).left)
        (SectionsOn E ((Over.star U).obj V).left) inferInstance
        (X.presheaf.map ((Over.forgetAdjStar U).counit.app V).op a) e := by
  rw [Over.forgetAdjStar_counit_app]
  rfl

set_option maxHeartbeats 1000000 in
/-- Extend a local derivation into the right-adjoint target. -/
def globalize {X S : Scheme} {s : X ⟶ S} {E : OModule X} {U : X.Opens}
    (D : LocalDerivation s E U) : RelativeSheafDerivation s (restrictionPushforward E U) where
  apply V a := D.apply ((Over.star U).obj V)
    (X.presheaf.map ((Over.forgetAdjStar U).counit.app V).op a)
  zero := by
    intro V
    change D.apply _ (X.presheaf.map _ 0) = 0
    rw [map_zero, D.zero]
  add := by
    intro V a b
    change D.apply ((Over.star U).obj V)
        (X.presheaf.map ((Over.forgetAdjStar U).counit.app V).op (a + b)) =
      D.apply ((Over.star U).obj V)
        (X.presheaf.map ((Over.forgetAdjStar U).counit.app V).op a) +
      D.apply ((Over.star U).obj V)
        (X.presheaf.map ((Over.forgetAdjStar U).counit.app V).op b)
    rw [map_add]
    exact D.add _ _ _
  leibniz := by
    intro V a b
    change D.apply ((Over.star U).obj V)
        (X.presheaf.map ((Over.forgetAdjStar U).counit.app V).op (a * b)) =
      @SMul.smul (RingSections X V) (SectionsOn (restrictionPushforward E U) V)
        inferInstance a (D.apply ((Over.star U).obj V)
          (X.presheaf.map ((Over.forgetAdjStar U).counit.app V).op b)) +
      @SMul.smul (RingSections X V) (SectionsOn (restrictionPushforward E U) V)
        inferInstance b (D.apply ((Over.star U).obj V)
          (X.presheaf.map ((Over.forgetAdjStar U).counit.app V).op a))
    rw [restrictionPushforward_smul, restrictionPushforward_smul, map_mul]
    exact D.leibniz _ _ _
  naturality := by
    intro V W i a
    change E.presheaf.map ((Over.star U).map i).left.op
        (D.apply ((Over.star U).obj W)
          (X.presheaf.map ((Over.forgetAdjStar U).counit.app W).op a)) =
      D.apply ((Over.star U).obj V)
        (X.presheaf.map ((Over.forgetAdjStar U).counit.app V).op
          (X.presheaf.map i.op a))
    have hD := D.naturality ((Over.star U).map i)
      (X.presheaf.map ((Over.forgetAdjStar U).counit.app W).op a)
    have hleft := ringRestrict_comp (X := X)
      ((Over.star U).map i).left ((Over.forgetAdjStar U).counit.app W) a
    have hright := ringRestrict_comp (X := X)
      ((Over.forgetAdjStar U).counit.app V) i a
    have hn : ((Over.star U).map i).left ≫ (Over.forgetAdjStar U).counit.app W =
        (Over.forgetAdjStar U).counit.app V ≫ i :=
      (Over.forgetAdjStar U).counit.naturality i
    have hmiddle := congrArg
      (fun j : ((Over.star U).obj V).left ⟶ W => X.presheaf.map j.op a) hn
    exact hD.trans (congrArg (D.apply ((Over.star U).obj V))
      (hleft.trans (hmiddle.trans hright.symm)))
  killsBase := by
    intro V a
    exact D.killsBase V a ((Over.star U).obj (s ⁻¹ᵁ V))
      ((Over.forgetAdjStar U).counit.app (s ⁻¹ᵁ V))

def localHomUnadjunct {X : Scheme} {M E : OModule X} {U : X.Opens}
    (g : M ⟶ restrictionPushforward E U) : M.over U ⟶ E.over U :=
  ((SheafOfModules.overPushforwardOverAdj (R := X.ringCatSheaf) U).homEquiv
    M (E.over U)).symm g

/-- The inverse adjunction evaluates by restricting along the unit. -/
theorem localHomUnadjunct_apply {X : Scheme} {M E : OModule X} {U : X.Opens}
    (g : M ⟶ restrictionPushforward E U) (W : Over U) (e : SectionsOn M W.left) :
    (localHomUnadjunct (M := M) (E := E) (U := U) g).val.app (op W) e =
      E.presheaf.map ((Over.forgetAdjStar U).unit.app W).left.op (g.app W.left e) := by
  rfl

/-- Surjective cotangent universality realizes every local relative
derivation on every subopen. The presentation is supplied explicitly. -/
theorem realize {X S : Scheme} {s : X ⟶ S}
    (P : CotangentPresentation s) (E : OModule X) (U : X.Opens)
    (D : LocalDerivation s E U) :
    ∃ φ : P.object.over U ⟶ E.over U,
      ∀ (W : Over U) (a : RingSections X W.left),
        φ.val.app (op W) (P.differential.apply W.left a) = D.apply W a := by
  obtain ⟨g, hg⟩ := (P.universal (restrictionPushforward E U)).2 (globalize D)
  refine ⟨localHomUnadjunct (M := P.object) (E := E) (U := U) g, ?_⟩
  intro W a
  rw [localHomUnadjunct_apply]
  have hg' := congrArg
    (fun D' : RelativeSheafDerivation s (restrictionPushforward E U) => D'.apply W.left a) hg
  change g.app W.left (P.differential.apply W.left a) =
    D.apply ((Over.star U).obj W.left)
      (X.presheaf.map ((Over.forgetAdjStar U).counit.app W.left).op a) at hg'
  have hres := congrArg
    (fun e : SectionsOn E ((Over.star U).obj W.left).left =>
      E.presheaf.map ((Over.forgetAdjStar U).unit.app W).left.op e) hg'
  have hn := D.naturality ((Over.forgetAdjStar U).unit.app W)
    (X.presheaf.map ((Over.forgetAdjStar U).counit.app W.left).op a)
  have hc := ringRestrict_comp (X := X)
    ((Over.forgetAdjStar U).unit.app W).left
    ((Over.forgetAdjStar U).counit.app W.left) a
  have htri : ((Over.forgetAdjStar U).unit.app W).left ≫
      (Over.forgetAdjStar U).counit.app W.left = 𝟙 W.left :=
    (Over.forgetAdjStar U).left_triangle_components W
  have hmap := congrArg (fun j : W.left ⟶ W.left => X.presheaf.map j.op a) htri
  have hid : X.presheaf.map (𝟙 W.left).op a = a := by simp
  exact hres.trans (hn.trans (congrArg (D.apply W) (hc.trans (hmap.trans hid))))

theorem realize_unique {X S : Scheme} {s : X ⟶ S}
    (P : CotangentPresentation s) (E : OModule X) (U : X.Opens)
    (D : LocalDerivation s E U) :
    ∃! φ : P.object.over U ⟶ E.over U,
      ∀ (W : Over U) (a : RingSections X W.left),
        φ.val.app (op W) (P.differential.apply W.left a) = D.apply W a := by
  obtain ⟨φ, hφ⟩ := realize P E U D
  refine ⟨φ, hφ, ?_⟩
  intro ψ hψ
  apply TangentFaithfulnessProof.restrictedCotangentHom_ext P E U
  intro W a
  exact (hψ W a).trans (hφ W a).symm

end LocalDerivationProof

end

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseThree

namespace TangentBracketProof

open LocalDerivationProof

abbrev restrictField {X S : Scheme} (s : X ⟶ S) (U : X.Opens)
    (v : SectionsOn (tangentSheaf s) U) (W : Over U) :
    SectionsOn (tangentSheaf s) W.left :=
  (tangentSheaf s).presheaf.map W.hom.op v

theorem restrictField_naturality {X S : Scheme} (s : X ⟶ S) (U : X.Opens)
    (v : SectionsOn (tangentSheaf s) U) {V W : Over U} (i : V ⟶ W) :
    (tangentSheaf s).presheaf.map i.left.op (restrictField s U v W) =
      restrictField s U v V := by
  change (tangentSheaf s).presheaf.map i.left.op
      ((tangentSheaf s).presheaf.map W.hom.op v) =
    (tangentSheaf s).presheaf.map V.hom.op v
  rw [moduleRestrict_comp, Over.w]

/-- A local vector need not extend to the whole inverse image of a base open.
The stored differential still kills a base function restricted to its domain. -/
theorem killsRestrictedBase {X S : Scheme} (s : X ⟶ S)
    (V : S.Opens) (W : X.Opens) (i : W ⟶ s ⁻¹ᵁ V)
    (v : SectionsOn (tangentSheaf s) W) (a : RingSections S V) :
    tangentActs s W v (X.presheaf.map i.op (s.app V a)) = 0 := by
  have hn := (cotangentPresentation s).differential.naturality i (s.app V a)
  rw [(cotangentPresentation s).differential.killsBase, map_zero] at hn
  change (tangentCotangentPair s).apply W v
    ((cotangentPresentation s).differential.apply W
      (X.presheaf.map i.op (s.app V a))) = 0
  rw [← hn, map_zero]

/-- The commutator of the two actual local actions, on every subopen. -/
def commutator {X S : Scheme} (s : X ⟶ S) (U : X.Opens)
    (v w : SectionsOn (tangentSheaf s) U) :
    LocalDerivation s (structureModule X) U where
  apply W a :=
    tangentActs s W.left (restrictField s U v W)
      (tangentActs s W.left (restrictField s U w W) a) -
    tangentActs s W.left (restrictField s U w W)
      (tangentActs s W.left (restrictField s U v W) a)
  zero := by
    intro W
    simp only [TangentActionProof.zero_function, sub_self]
  add := by
    intro W a b
    simp only [TangentActionProof.add_function]
    abel
  leibniz := by
    intro W a b
    change
      tangentActs s W.left (restrictField s U v W)
          (tangentActs s W.left (restrictField s U w W) (a * b)) -
        tangentActs s W.left (restrictField s U w W)
          (tangentActs s W.left (restrictField s U v W) (a * b)) =
      a * (tangentActs s W.left (restrictField s U v W)
          (tangentActs s W.left (restrictField s U w W) b) -
        tangentActs s W.left (restrictField s U w W)
          (tangentActs s W.left (restrictField s U v W) b)) +
      b * (tangentActs s W.left (restrictField s U v W)
          (tangentActs s W.left (restrictField s U w W) a) -
        tangentActs s W.left (restrictField s U w W)
          (tangentActs s W.left (restrictField s U v W) a))
    simp only [TangentActionProof.leibniz, TangentActionProof.add_function]
    ring
  naturality := by
    intro V W i a
    change X.presheaf.map i.left.op
        (tangentActs s W.left (restrictField s U v W)
            (tangentActs s W.left (restrictField s U w W) a) -
          tangentActs s W.left (restrictField s U w W)
            (tangentActs s W.left (restrictField s U v W) a)) = _
    simp only [map_sub, TangentActionProof.naturality, restrictField_naturality]
  killsBase := by
    intro V a W i
    simp only [killsRestrictedBase, TangentActionProof.zero_function, sub_self]

/-- The given intrinsic dual section as its actual local module morphism. -/
def localFunctional {X S : Scheme} (s : X ⟶ S) (U : X.Opens)
    (v : SectionsOn (tangentSheaf s) U) :
    (cotangentSheaf s).over U ⟶ (structureModule X).over U :=
  HomConstruction.Generic.sectionOverEquiv (R := X.sheaf)
    (cotangentSheaf s) (structureModule X) U
    ((internalHomGenericIso (cotangentSheaf s) (structureModule X)).hom.app U v)

theorem localFunctional_apply {X S : Scheme} (s : X ⟶ S) (U : X.Opens)
    (v : SectionsOn (tangentSheaf s) U) (W : Over U) (a : RingSections X W.left) :
    (localFunctional s U v).val.app (op W)
        ((cotangentPresentation s).differential.apply W.left a) =
      tangentActs s W.left ((tangentSheaf s).presheaf.map W.hom.op v) a := by
  let e := internalHomGenericIso (cotangentSheaf s) (structureModule X)
  have hn := sheafHom_naturality e.hom W.hom v
  change HomConstruction.Generic.restrictSection W.hom (e.hom.app U v) =
    e.hom.app W.left ((tangentSheaf s).presheaf.map W.hom.op v) at hn
  calc
    _ = HomConstruction.Generic.evaluationAt (R := X.sheaf) (cotangentSheaf s) (structureModule X)
        W.left (HomConstruction.Generic.restrictSection W.hom (e.hom.app U v))
        ((cotangentPresentation s).differential.apply W.left a) := by
      exact (HomConstruction.Generic.evaluationAt_restrict (R := X.sheaf) W.hom (e.hom.app U v)
        ((cotangentPresentation s).differential.apply W.left a)).symm
    _ = HomConstruction.Generic.evaluationAt (R := X.sheaf) (cotangentSheaf s) (structureModule X)
        W.left (e.hom.app W.left ((tangentSheaf s).presheaf.map W.hom.op v))
        ((cotangentPresentation s).differential.apply W.left a) := by rw [hn]
    _ = _ := internalHomGenericIso_evaluate_pair (cotangentSheaf s) (structureModule X)
      W.left ((tangentSheaf s).presheaf.map W.hom.op v)
      ((cotangentPresentation s).differential.apply W.left a)

theorem localFunctional_surjective {X S : Scheme} (s : X ⟶ S) (U : X.Opens) :
    Function.Surjective (localFunctional s U) := by
  intro φ
  let e := internalHomGenericIso (cotangentSheaf s) (structureModule X)
  let q := (HomConstruction.Generic.sectionOverEquiv (R := X.sheaf)
    (cotangentSheaf s) (structureModule X) U).symm φ
  refine ⟨e.inv.app U q, ?_⟩
  change HomConstruction.Generic.sectionOverEquiv (R := X.sheaf)
    (cotangentSheaf s) (structureModule X) U (e.hom.app U (e.inv.app U q)) = φ
  have he : e.hom.app U (e.inv.app U q) = q := by
    change (e.inv ≫ e.hom).app U q = q
    rw [e.inv_hom_id]
    rfl
  rw [he]
  exact (HomConstruction.Generic.sectionOverEquiv (R := X.sheaf)
    (cotangentSheaf s) (structureModule X) U).apply_symm_apply φ

/-- The original all-subopens existence-and-uniqueness statement. -/
theorem tangentBracket_existsUnique {X S : Scheme} (s : X ⟶ S)
    (U : X.Opens) (v w : SectionsOn (tangentSheaf s) U) :
    ∃! z : SectionsOn (tangentSheaf s) U,
      ∀ (V : X.Opens) (i : V ⟶ U) (a : RingSections X V),
        tangentActs s V ((tangentSheaf s).presheaf.map i.op z) a =
          tangentActs s V ((tangentSheaf s).presheaf.map i.op v)
            (tangentActs s V ((tangentSheaf s).presheaf.map i.op w) a) -
          tangentActs s V ((tangentSheaf s).presheaf.map i.op w)
            (tangentActs s V ((tangentSheaf s).presheaf.map i.op v) a) := by
  obtain ⟨φ, hφ⟩ := LocalDerivationProof.realize (cotangentPresentation s)
    (structureModule X) U (commutator s U v w)
  obtain ⟨z, hz⟩ := localFunctional_surjective s U φ
  have hcomm : ∀ (V : X.Opens) (i : V ⟶ U) (a : RingSections X V),
      tangentActs s V ((tangentSheaf s).presheaf.map i.op z) a =
        tangentActs s V ((tangentSheaf s).presheaf.map i.op v)
          (tangentActs s V ((tangentSheaf s).presheaf.map i.op w) a) -
        tangentActs s V ((tangentSheaf s).presheaf.map i.op w)
          (tangentActs s V ((tangentSheaf s).presheaf.map i.op v) a) := by
    intro V i a
    have hlocal :
        (localFunctional s U z).val.app (op (Over.mk i))
            ((cotangentPresentation s).differential.apply V a) =
          tangentActs s V ((tangentSheaf s).presheaf.map i.op z) a :=
      localFunctional_apply s U z (Over.mk i) a
    have heq := congrArg
      (fun ψ : (cotangentSheaf s).over U ⟶ (structureModule X).over U =>
        ψ.val.app (op (Over.mk i)) ((cotangentPresentation s).differential.apply V a)) hz
    exact hlocal.symm.trans (heq.trans (hφ (Over.mk i) a))
  refine ⟨z, hcomm, ?_⟩
  intro y hy
  apply tangentActs_faithful s U
  intro V i a
  exact (hy V i a).trans (hcomm V i a).symm

end TangentBracketProof

end

/-- The bracket is characterized on ALL SUBOPENS. Testing only O(U) is insufficient: on a connected proper
complex variety global regular functions are constant, although vector fields need not vanish. -/
theorem tangentBracket_existsUnique {X S : Scheme} (s : X ⟶ S)
    (U : X.Opens) (v w : SectionsOn (tangentSheaf s) U) :
    ∃! z : SectionsOn (tangentSheaf s) U,
      ∀ (V : X.Opens) (i : V ⟶ U) (a : RingSections X V),
        tangentActs s V ((tangentSheaf s).presheaf.map i.op z) a =
          tangentActs s V ((tangentSheaf s).presheaf.map i.op v)
            (tangentActs s V ((tangentSheaf s).presheaf.map i.op w) a) -
          tangentActs s V ((tangentSheaf s).presheaf.map i.op w)
            (tangentActs s V ((tangentSheaf s).presheaf.map i.op v) a) := by
  exact TangentBracketProof.tangentBracket_existsUnique s U v w

def tangentBracket {X S : Scheme} (s : X ⟶ S)
    (U : X.Opens) (v w : SectionsOn (tangentSheaf s) U) :
    SectionsOn (tangentSheaf s) U :=
  Classical.choose (tangentBracket_existsUnique s U v w)

theorem tangentBracket_spec_on {X S : Scheme} (s : X ⟶ S)
    (U : X.Opens) (v w : SectionsOn (tangentSheaf s) U)
    (V : X.Opens) (i : V ⟶ U) (a : RingSections X V) :
    tangentActs s V ((tangentSheaf s).presheaf.map i.op (tangentBracket s U v w)) a =
      tangentActs s V ((tangentSheaf s).presheaf.map i.op v)
        (tangentActs s V ((tangentSheaf s).presheaf.map i.op w) a) -
      tangentActs s V ((tangentSheaf s).presheaf.map i.op w)
        (tangentActs s V ((tangentSheaf s).presheaf.map i.op v) a) :=
  (Classical.choose_spec (tangentBracket_existsUnique s U v w)).1 V i a

set_option backward.isDefEq.respectTransparency false in
theorem tangentActs_add_field {X S : Scheme} (s : X ⟶ S)
    (U : X.Opens) (v w : SectionsOn (tangentSheaf s) U) (a : RingSections X U) :
    tangentActs s U (v + w) a = tangentActs s U v a + tangentActs s U w a := by
  simp [tangentActs]

set_option backward.isDefEq.respectTransparency false in
theorem tangentActs_add_function {X S : Scheme} (s : X ⟶ S)
    (U : X.Opens) (v : SectionsOn (tangentSheaf s) U) (a b : RingSections X U) :
    tangentActs s U v (a + b) = tangentActs s U v a + tangentActs s U v b := by
  simp [tangentActs, (cotangentPresentation s).differential.add]

theorem tangentBracket_add_left {X S : Scheme} (s : X ⟶ S)
    (U : X.Opens) (u v w : SectionsOn (tangentSheaf s) U) :
    tangentBracket s U (u + v) w = tangentBracket s U u w + tangentBracket s U v w := by
  apply tangentActs_faithful s U
  intro V i a
  rw [tangentBracket_spec_on]
  simp only [map_add, tangentActs_add_field, tangentActs_add_function,
    tangentBracket_spec_on]
  ring

theorem tangentBracket_add_right {X S : Scheme} (s : X ⟶ S)
    (U : X.Opens) (u v w : SectionsOn (tangentSheaf s) U) :
    tangentBracket s U u (v + w) = tangentBracket s U u v + tangentBracket s U u w := by
  apply tangentActs_faithful s U
  intro V i a
  rw [tangentBracket_spec_on]
  simp only [map_add, tangentActs_add_field, tangentActs_add_function,
    tangentBracket_spec_on]
  ring

theorem tangentBracket_spec {X S : Scheme} (s : X ⟶ S)
    (U : X.Opens) (v w : SectionsOn (tangentSheaf s) U)
    (a : RingSections X U) :
    tangentActs s U (tangentBracket s U v w) a =
      tangentActs s U v (tangentActs s U w a) -
        tangentActs s U w (tangentActs s U v a) := by
  simpa using tangentBracket_spec_on s U v w U (𝟙 U) a

noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive

namespace TangentBracketProof

theorem restrict_smul {X S : Scheme} (s : X ⟶ S)
    {U V : X.Opens} (i : U ⟶ V) (a : RingSections X V)
    (v : SectionsOn (tangentSheaf s) V) :
    (tangentSheaf s).presheaf.map i.op (a • v) =
      X.presheaf.map i.op a • (tangentSheaf s).presheaf.map i.op v :=
  (tangentSheaf s).val.map_smul i.op a v

theorem skew {X S : Scheme} (s : X ⟶ S)
    (U : X.Opens) (v w : SectionsOn (tangentSheaf s) U) :
    tangentBracket s U v w = -tangentBracket s U w v := by
  apply tangentActs_faithful s U
  intro V i a
  simp only [map_neg, TangentActionProof.neg_field, tangentBracket_spec_on]
  ring

theorem self_eq_zero {X S : Scheme} (s : X ⟶ S)
    (U : X.Opens) (v : SectionsOn (tangentSheaf s) U) :
    tangentBracket s U v v = 0 := by
  apply tangentActs_faithful s U
  intro V i a
  simp only [map_zero, TangentActionProof.zero_field, tangentBracket_spec_on, sub_self]

theorem zero_left {X S : Scheme} (s : X ⟶ S)
    (U : X.Opens) (v : SectionsOn (tangentSheaf s) U) :
    tangentBracket s U 0 v = 0 := by
  apply tangentActs_faithful s U
  intro V i a
  simp only [map_zero, tangentBracket_spec_on, TangentActionProof.zero_field,
    TangentActionProof.zero_function, sub_self]

theorem zero_right {X S : Scheme} (s : X ⟶ S)
    (U : X.Opens) (v : SectionsOn (tangentSheaf s) U) :
    tangentBracket s U v 0 = 0 := by
  apply tangentActs_faithful s U
  intro V i a
  simp only [map_zero, tangentBracket_spec_on, TangentActionProof.zero_field,
    TangentActionProof.zero_function, sub_self]

theorem jacobi {X S : Scheme} (s : X ⟶ S)
    (U : X.Opens) (u v w : SectionsOn (tangentSheaf s) U) :
    tangentBracket s U u (tangentBracket s U v w) +
      tangentBracket s U v (tangentBracket s U w u) +
      tangentBracket s U w (tangentBracket s U u v) = 0 := by
  apply tangentActs_faithful s U
  intro V i a
  simp only [map_add, map_zero, TangentActionProof.add_field,
    TangentActionProof.zero_field, tangentBracket_spec_on, TangentActionProof.sub_function]
  ring

theorem leibniz {X S : Scheme} (s : X ⟶ S)
    (U : X.Opens) (v w : SectionsOn (tangentSheaf s) U)
    (a : RingSections X U) :
    tangentBracket s U v (a • w) =
      tangentActs s U v a • w + a • tangentBracket s U v w := by
  apply tangentActs_faithful s U
  intro V i b
  simp only [tangentBracket_spec_on, map_add, restrict_smul,
    TangentActionProof.add_field, TangentActionProof.smul_field,
    TangentActionProof.leibniz, TangentActionProof.naturality]
  ring

end TangentBracketProof

end

theorem tangentBracket_skew {X S : Scheme} (s : X ⟶ S)
    (U : X.Opens) (v w : SectionsOn (tangentSheaf s) U) :
    tangentBracket s U v w = -tangentBracket s U w v := by
  exact TangentBracketProof.skew s U v w

theorem tangentBracket_jacobi {X S : Scheme} (s : X ⟶ S)
    (U : X.Opens) (u v w : SectionsOn (tangentSheaf s) U) :
    tangentBracket s U u (tangentBracket s U v w) +
      tangentBracket s U v (tangentBracket s U w u) +
      tangentBracket s U w (tangentBracket s U u v) = 0 := by
  exact TangentBracketProof.jacobi s U u v w

theorem tangentBracket_leibniz {X S : Scheme} (s : X ⟶ S)
    (U : X.Opens) (v w : SectionsOn (tangentSheaf s) U)
    (a : RingSections X U) :
    tangentBracket s U v (a • w) =
      tangentActs s U v a • w + a • tangentBracket s U v w := by
  exact TangentBracketProof.leibniz s U v w a

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseThree

namespace TangentBracketProof

open LocalDerivationProof

/-- Exact original restriction statement. Its reference to the old bracket
choice retains the old existence leaf until that original name is replaced. -/
theorem tangentBracket_restrict {X S : Scheme} (s : X ⟶ S)
    {U V : X.Opens} (i : U ⟶ V)
    (v w : SectionsOn (tangentSheaf s) V) :
    (tangentSheaf s).presheaf.map i.op (tangentBracket s V v w) =
      tangentBracket s U ((tangentSheaf s).presheaf.map i.op v)
        ((tangentSheaf s).presheaf.map i.op w) := by
  apply tangentActs_faithful s U
  intro W j a
  simp only [moduleRestrict_comp, PhaseTwentyFive.tangentBracket_spec_on]

end TangentBracketProof

end

theorem tangentBracket_restrict {X S : Scheme} (s : X ⟶ S)
    {U V : X.Opens} (i : U ⟶ V)
    (v w : SectionsOn (tangentSheaf s) V) :
    (tangentSheaf s).presheaf.map i.op (tangentBracket s V v w) =
      tangentBracket s U ((tangentSheaf s).presheaf.map i.op v)
        ((tangentSheaf s).presheaf.map i.op w) := by
  exact TangentBracketProof.tangentBracket_restrict s i v w

end LeBrunSalamon.PhaseTwentyFive

/-!
# Phase 26 -- exterior powers, determinants, and positivity

Existence of the representing sheaves is an explicit FOUNDATION obligation. Definitions use their
universal properties. Ampleness is specified by affine nonvanishing loci of positive tensor powers, not by
an arbitrary predicate on a line-bundle label. See Stacks 01CF, 01PR.
-/

namespace LeBrunSalamon.PhaseTwentySix

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseTwentyFive

/-- Alternating multilinear sheaf maps. For r=0 this correctly amounts
to a section of the target; no positive-rank assumption is concealed. -/
structure SheafAlternatingMap {X : Scheme} (E F : OModule X) (r : ℕ) where
  apply : ∀ U : X.Opens, (Fin r → SectionsOn E U) → SectionsOn F U
  add_slot : ∀ U v i a b,
    apply U (Function.update v i (a + b)) =
      apply U (Function.update v i a) + apply U (Function.update v i b)
  smul_slot : ∀ U v i (a : RingSections X U) w,
    apply U (Function.update v i (a • w)) =
      a • apply U (Function.update v i w)
  alternating : ∀ U v i j, i ≠ j → v i = v j → apply U v = 0
  naturality : ∀ {U V : X.Opens} (i : U ⟶ V) v,
    F.presheaf.map i.op (apply V v) =
      apply U (fun j => E.presheaf.map i.op (v j))

def SheafAlternatingMap.postcompose {X : Scheme}
    {E F G : OModule X} {r : ℕ}
    (a : SheafAlternatingMap E F r) (h : F ⟶ G) :
    SheafAlternatingMap E G r where
  apply U v := h.app U (a.apply U v)
  add_slot := by intros; simp [a.add_slot]
  smul_slot := by intros; simp [a.smul_slot]
  alternating := by
    intro U v i j hij heq
    exact (congrArg (fun w => h.app U w) (a.alternating U v i j hij heq)).trans (map_zero _)
  naturality := by
    intro U V i v
    rw [sheafHom_naturality, a.naturality]

structure ExteriorPresentation {X : Scheme} (E : OModule X) (r : ℕ) where
  object : OModule X
  wedge : SheafAlternatingMap E object r
  universal : ∀ F : OModule X,
    Function.Bijective (fun h : object ⟶ F => wedge.postcompose h)

/-- **Published input (exact).** The `r`-th exterior power represents
alternating `r`-linear maps.  This is the universal property defining
exterior powers in Stacks Project, Section 17.21 (Tag 01CF), translated
literally to sheaves of modules. -/
theorem _root_.LeBrunSalamon.PublishedInputs.SheafFunctoriality.exteriorPresentation
    {X : Scheme} (E : OModule X) (r : ℕ) :
    Nonempty (ExteriorPresentation E r) := by
  sorry

/-- Project API wrapper for the exact exterior-power input. -/
theorem exteriorPresentation_exists {X : Scheme} (E : OModule X) (r : ℕ) :
    Nonempty (ExteriorPresentation E r) :=
  LeBrunSalamon.PublishedInputs.SheafFunctoriality.exteriorPresentation E r

def exteriorPresentation {X : Scheme} (E : OModule X) (r : ℕ) :
    ExteriorPresentation E r :=
  Classical.choice (exteriorPresentation_exists E r)

abbrev exteriorSheaf {X : Scheme} (E : OModule X) (r : ℕ) : OModule X :=
  (exteriorPresentation E r).object

def exteriorLift {X : Scheme} {E F : OModule X} {r : ℕ}
    (a : SheafAlternatingMap E F r) : exteriorSheaf E r ⟶ F :=
  (Equiv.ofBijective
    (fun h : exteriorSheaf E r ⟶ F =>
      (exteriorPresentation E r).wedge.postcompose h)
    ((exteriorPresentation E r).universal F)).symm a

theorem exteriorLift_spec {X : Scheme} {E F : OModule X} {r : ℕ}
    (a : SheafAlternatingMap E F r) :
    (exteriorPresentation E r).wedge.postcompose (exteriorLift a) = a := by
  set_option backward.isDefEq.respectTransparency false in
    exact (Equiv.ofBijective
      (fun h : exteriorSheaf E r ⟶ F =>
        (exteriorPresentation E r).wedge.postcompose h)
      ((exteriorPresentation E r).universal F)).apply_symm_apply a

/- Ordinary universal-property proofs for exterior powers in arities zero and one.
   Insert immediately before the original exteriorSheaf_zero declaration. -/
section SmallExteriorPowerProofSection
set_option backward.isDefEq.respectTransparency false

namespace SmallExteriorPowerProof

theorem alternating_ext {X : Scheme} {E F : OModule X} {r : ℕ}
    (a b : SheafAlternatingMap E F r)
    (h : ∀ U v, a.apply U v = b.apply U v) : a = b := by
  cases a
  cases b
  congr 1
  funext U v
  exact h U v

theorem postcompose_id {X : Scheme} {E F : OModule X} {r : ℕ}
    (a : SheafAlternatingMap E F r) : a.postcompose (𝟙 F) = a := by
  cases a
  rfl

theorem postcompose_comp {X : Scheme} {E F G H : OModule X} {r : ℕ}
    (a : SheafAlternatingMap E F r) (f : F ⟶ G) (g : G ⟶ H) :
    a.postcompose (f ≫ g) = (a.postcompose f).postcompose g := by
  rfl

theorem presentation_unique {X : Scheme} {E : OModule X} {r : ℕ}
    (P Q : ExteriorPresentation E r) : Nonempty (P.object ≅ Q.object) := by
  obtain ⟨f, hf⟩ := (P.universal Q.object).2 Q.wedge
  obtain ⟨g, hg⟩ := (Q.universal P.object).2 P.wedge
  change P.wedge.postcompose f = Q.wedge at hf
  change Q.wedge.postcompose g = P.wedge at hg
  refine ⟨{ hom := f, inv := g, hom_inv_id := ?_, inv_hom_id := ?_ }⟩
  · apply (P.universal P.object).1
    change P.wedge.postcompose (f ≫ g) = P.wedge.postcompose (𝟙 P.object)
    rw [postcompose_comp, hf, hg, postcompose_id]
  · apply (Q.universal Q.object).1
    change Q.wedge.postcompose (g ≫ f) = Q.wedge.postcompose (𝟙 Q.object)
    rw [postcompose_comp, hg, hf, postcompose_id]

def zeroWedge {X : Scheme} (E : OModule X) :
    SheafAlternatingMap E (structureModule X) 0 where
  apply U _ := (1 : RingSections X U)
  add_slot := by intro U v i; exact Fin.elim0 i
  smul_slot := by intro U v i; exact Fin.elim0 i
  alternating := by intro U v i; exact Fin.elim0 i
  naturality := by
    intro U V i v
    exact PresheafOfModules.unit_map_one X.ringCatSheaf.obj i.op

def zeroSection {X : Scheme} {E F : OModule X}
    (a : SheafAlternatingMap E F 0) : F.sections where
  val U := a.apply U.unop (fun i => Fin.elim0 i)
  property := by
    intro U V i
    exact (a.naturality i.unop (fun j => Fin.elim0 j)).trans
      (congrArg (a.apply V.unop) (Subsingleton.elim _ _))

def zeroPresentation {X : Scheme} (E : OModule X) :
    ExteriorPresentation E 0 where
  object := structureModule X
  wedge := zeroWedge E
  universal F := by
    constructor
    · intro f g h
      apply F.unitHomEquiv.injective
      apply PresheafOfModules.sections_ext
      intro U
      exact congrArg
        (fun a : SheafAlternatingMap E F 0 =>
          a.apply U.unop (fun i => Fin.elim0 i)) h
    · intro a
      refine ⟨F.unitHomEquiv.symm (zeroSection a), ?_⟩
      apply alternating_ext
      intro U v
      have h := congrArg (fun s : F.sections => s.val (Opposite.op U))
        (F.unitHomEquiv.apply_symm_apply (zeroSection a))
      change (F.unitHomEquiv.symm (zeroSection a)).val.app (Opposite.op U)
        (1 : RingSections X U) = a.apply U (fun i => Fin.elim0 i) at h
      exact h.trans (congrArg (a.apply U) (Subsingleton.elim _ _))

theorem update_one {A : Type*} (v : Fin 1 → A) (a : A) :
    Function.update v 0 a = fun _ => a := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp

def oneWedge {X : Scheme} (E : OModule X) : SheafAlternatingMap E E 1 where
  apply U v := v 0
  add_slot := by
    intro U v i a b
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp
  smul_slot := by
    intro U v i a b
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp
  alternating := by
    intro U v i j hij
    exact (hij (Subsingleton.elim _ _)).elim
  naturality := by intros; rfl

def oneLinear {X : Scheme} {E F : OModule X}
    (a : SheafAlternatingMap E F 1) (U : X.Opens) :
    SectionsOn E U →ₗ[RingSections X U] SectionsOn F U where
  toFun v := a.apply U (fun _ => v)
  map_add' v w := by
    simpa only [update_one] using a.add_slot U (fun _ => 0) 0 v w
  map_smul' c v := by
    simpa only [update_one, RingHom.id_apply] using a.smul_slot U (fun _ => 0) 0 c v

def oneHom {X : Scheme} {E F : OModule X}
    (a : SheafAlternatingMap E F 1) : E ⟶ F where
  val := PresheafOfModulesOfCommRing.homMk
    (fun U => ModuleCat.ofHom (X := E.val.obj U) (Y := F.val.obj U)
      (oneLinear a U.unop))
    (by
      intro U V i
      ext v
      exact (a.naturality i.unop (fun _ => v)).symm)

def onePresentation {X : Scheme} (E : OModule X) :
    ExteriorPresentation E 1 where
  object := E
  wedge := oneWedge E
  universal F := by
    constructor
    · intro f g h
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro U
      ext v
      exact congrArg
        (fun a : SheafAlternatingMap E F 1 => a.apply U.unop (fun _ => v)) h
    · intro a
      refine ⟨oneHom a, ?_⟩
      apply alternating_ext
      intro U v
      change a.apply U (fun _ => v 0) = a.apply U v
      apply congrArg (a.apply U)
      funext i
      exact congrArg v (Subsingleton.elim _ _)

end SmallExteriorPowerProof
end SmallExteriorPowerProofSection



theorem exteriorSheaf_zero {X : Scheme} (E : OModule X) :
    Nonempty (exteriorSheaf E 0 ≅ structureModule X) := by
  exact SmallExteriorPowerProof.presentation_unique
    (exteriorPresentation E 0) (SmallExteriorPowerProof.zeroPresentation E)

theorem exteriorSheaf_one {X : Scheme} (E : OModule X) :
    Nonempty (exteriorSheaf E 1 ≅ E) := by
  exact SmallExteriorPowerProof.presentation_unique
    (exteriorPresentation E 1) (SmallExteriorPowerProof.onePresentation E)

/-- **Published input (exact).** The `r`-th exterior power of a finite
locally free module of rank `d` is finite locally free of rank `d.choose r`.
This is Stacks Project, Lemma 17.21.5(6) (Section 17.21, Tag 01CF), with
the standard finite-free rank computation. -/
theorem _root_.LeBrunSalamon.PublishedInputs.SheafFunctoriality.exterior_locallyFree
    {X : Scheme} {E : OModule X} {d : ℕ}
    (hE : IsLocallyFreeOfRank E d) (r : ℕ) :
    IsLocallyFreeOfRank (exteriorSheaf E r) (Nat.choose d r) := by
  sorry

/-- **Published input (exact).** Pullback commutes with exterior powers;
this is Stacks Project, Lemma 17.21.3 (Section 17.21, Tag 01CF). -/
theorem _root_.LeBrunSalamon.PublishedInputs.SheafFunctoriality.pullback_exterior
    {X Y : Scheme} (f : X ⟶ Y) (E : OModule Y) (r : ℕ) :
    Nonempty (pullbackModule f (exteriorSheaf E r) ≅
      exteriorSheaf (pullbackModule f E) r) := by
  sorry

/-- Project API wrapper for the finite-locally-free exterior-power theorem. -/
theorem exteriorSheaf_locallyFree {X : Scheme} {E : OModule X}
    {d : ℕ} (hE : IsLocallyFreeOfRank E d) (r : ℕ) :
    IsLocallyFreeOfRank (exteriorSheaf E r) (Nat.choose d r) :=
  LeBrunSalamon.PublishedInputs.SheafFunctoriality.exterior_locallyFree hE r

/-- Project API wrapper for exact pullback functoriality of exterior powers. -/
theorem exteriorSheaf_pullback {X Y : Scheme} (f : X ⟶ Y)
    (E : OModule Y) (r : ℕ) :
    Nonempty (pullbackModule f (exteriorSheaf E r) ≅
      exteriorSheaf (pullbackModule f E) r) :=
  LeBrunSalamon.PublishedInputs.SheafFunctoriality.pullback_exterior f E r

/-- Symmetric multilinear maps are used for diagonal symbols. This is
not an assertion that the symbol of an arbitrary section is contact. -/
structure SheafSymmetricMap {X : Scheme} (E F : OModule X) (r : ℕ) where
  apply : ∀ U : X.Opens, (Fin r → SectionsOn E U) → SectionsOn F U
  add_slot : ∀ U v i a b,
    apply U (Function.update v i (a + b)) =
      apply U (Function.update v i a) + apply U (Function.update v i b)
  smul_slot : ∀ U v i (a : RingSections X U) w,
    apply U (Function.update v i (a • w)) =
      a • apply U (Function.update v i w)
  symmetric : ∀ U v (e : Equiv.Perm (Fin r)), apply U (v ∘ e) = apply U v
  naturality : ∀ {U V : X.Opens} (i : U ⟶ V) v,
    F.presheaf.map i.op (apply V v) =
      apply U (fun j => E.presheaf.map i.op (v j))

def SheafSymmetricMap.postcompose {X : Scheme} {E F G : OModule X}
    {r : ℕ} (a : SheafSymmetricMap E F r) (h : F ⟶ G) :
    SheafSymmetricMap E G r where
  apply U v := h.app U (a.apply U v)
  add_slot := by intros; simp [a.add_slot]
  smul_slot := by intros; simp [a.smul_slot]
  symmetric := by intros; simp [a.symmetric]
  naturality := by
    intro U V i v
    rw [sheafHom_naturality, a.naturality]

structure SymmetricPresentation {X : Scheme} (E : OModule X) (r : ℕ) where
  object : OModule X
  product : SheafSymmetricMap E object r
  universal : ∀ F : OModule X,
    Function.Bijective (fun h : object ⟶ F => product.postcompose h)

/-- **Published input (exact).** The `r`-th symmetric power represents
symmetric `r`-linear maps.  This is the universal property defining
symmetric powers in Stacks Project, Section 17.21 (Tag 01CF), translated
literally to sheaves of modules. -/
theorem _root_.LeBrunSalamon.PublishedInputs.SheafFunctoriality.symmetricPresentation
    {X : Scheme} (E : OModule X) (r : ℕ) :
    Nonempty (SymmetricPresentation E r) := by
  sorry

/-- Project API wrapper for the exact symmetric-power input. -/
theorem symmetricPresentation_exists {X : Scheme} (E : OModule X) (r : ℕ) :
    Nonempty (SymmetricPresentation E r) :=
  LeBrunSalamon.PublishedInputs.SheafFunctoriality.symmetricPresentation E r

def symmetricPresentation {X : Scheme} (E : OModule X) (r : ℕ) :
    SymmetricPresentation E r :=
  Classical.choice (symmetricPresentation_exists E r)

abbrev symmetricSheaf {X : Scheme} (E : OModule X) (r : ℕ) : OModule X :=
  (symmetricPresentation E r).object

/- At arities zero and one the symmetry and alternation conditions impose no
   extra relation. Insert immediately before the original symmetricSheaf_zero. -/
section SmallSymmetricPowerProofSection
set_option backward.isDefEq.respectTransparency false

namespace SmallSymmetricPowerProof

def toAlternating {X : Scheme} {E F : OModule X} {r : ℕ}
    [Subsingleton (Fin r)] (a : SheafSymmetricMap E F r) :
    SheafAlternatingMap E F r where
  apply := a.apply
  add_slot := a.add_slot
  smul_slot := a.smul_slot
  alternating := by
    intro U v i j hij
    exact (hij (Subsingleton.elim _ _)).elim
  naturality := a.naturality

def toSymmetric {X : Scheme} {E F : OModule X} {r : ℕ}
    [Subsingleton (Fin r)] (a : SheafAlternatingMap E F r) :
    SheafSymmetricMap E F r where
  apply := a.apply
  add_slot := a.add_slot
  smul_slot := a.smul_slot
  symmetric := by
    intro U v e
    apply congrArg (a.apply U)
    funext i
    exact congrArg v (Subsingleton.elim _ _)
  naturality := a.naturality

def mapEquiv {X : Scheme} (E F : OModule X) (r : ℕ)
    [Subsingleton (Fin r)] :
    SheafSymmetricMap E F r ≃ SheafAlternatingMap E F r where
  toFun := toAlternating
  invFun := toSymmetric
  left_inv a := by cases a; rfl
  right_inv a := by cases a; rfl

def alternatingPresentation {X : Scheme} (E : OModule X) (r : ℕ)
    [Subsingleton (Fin r)] : ExteriorPresentation E r where
  object := symmetricSheaf E r
  wedge := toAlternating (symmetricPresentation E r).product
  universal F := by
    exact (mapEquiv E F r).bijective.comp ((symmetricPresentation E r).universal F)

theorem symmetric_exterior {X : Scheme} (E : OModule X) (r : ℕ)
    [Subsingleton (Fin r)] : Nonempty (symmetricSheaf E r ≅ exteriorSheaf E r) :=
  SmallExteriorPowerProof.presentation_unique
    (alternatingPresentation E r) (exteriorPresentation E r)

end SmallSymmetricPowerProof
end SmallSymmetricPowerProofSection



theorem symmetricSheaf_zero {X : Scheme} (E : OModule X) :
    Nonempty (symmetricSheaf E 0 ≅ structureModule X) := by
  obtain ⟨e⟩ := SmallSymmetricPowerProof.symmetric_exterior E 0
  obtain ⟨e₀⟩ := exteriorSheaf_zero E
  exact ⟨e ≪≫ e₀⟩

theorem symmetricSheaf_one {X : Scheme} (E : OModule X) :
    Nonempty (symmetricSheaf E 1 ≅ E) := by
  obtain ⟨e⟩ := SmallSymmetricPowerProof.symmetric_exterior E 1
  obtain ⟨e₁⟩ := exteriorSheaf_one E
  exact ⟨e ≪≫ e₁⟩


set_option backward.isDefEq.respectTransparency false in
theorem locallyFreeOfRank_iso {X : Scheme} {E F : OModule X}
    (e : E ≅ F) {r : ℕ} (hE : IsLocallyFreeOfRank E r) :
    IsLocallyFreeOfRank F r := by
  obtain ⟨q, hq, hr⟩ := hE
  letI := hq
  let q' : SheafOfModules.LocalGeneratorsData.{0} F :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators := fun i => (q.generators i).ofEpi
        ((SheafOfModules.overFunctor X.ringCatSheaf (q.X i)).map e.hom) }
  refine ⟨q', ?_, hr⟩
  constructor
  intro i
  change IsIso ((q.generators i).ofEpi _).π
  rw [SheafOfModules.GeneratingSections.ofEpi_π]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
theorem freeSheaf_rank (X : Scheme) (r : ℕ) :
    IsLocallyFreeOfRank (SheafOfModules.free (R := X.ringCatSheaf) (Fin r)) r := by
  let q := (SheafOfModules.free.generatingSections
    (R := X.ringCatSheaf) (Fin r)).localGeneratorsData
  exact ⟨q, inferInstance, fun _ => ⟨Equiv.refl _⟩⟩

set_option backward.isDefEq.respectTransparency false in
theorem structureModule_rank (X : Scheme) :
    IsLocallyFreeOfRank (structureModule X) 1 := by
  exact locallyFreeOfRank_iso
    (coproductUniqueIso (fun _ : Fin 1 => SheafOfModules.unit X.ringCatSheaf))
    (freeSheaf_rank X 1)

/-- **Published input (exact).** Pullback preserves finite local
freeness and its constant rank.  This is Stacks Project, Lemma 17.14.3
(Section 17.14, Tag 01C5), with the rank read on the standard pulled-back
local trivializations. -/
theorem _root_.LeBrunSalamon.PublishedInputs.SheafFunctoriality.pullback_locallyFree
    {X Y : Scheme} (f : X ⟶ Y) {E : OModule Y} {r : ℕ}
    (hE : IsLocallyFreeOfRank E r) :
    IsLocallyFreeOfRank (pullbackModule f E) r := by
  sorry

/-- Project API wrapper for exact preservation of finite local freeness. -/
theorem pullback_locallyFree {X Y : Scheme} (f : X ⟶ Y)
    {E : OModule Y} {r : ℕ} (hE : IsLocallyFreeOfRank E r) :
    IsLocallyFreeOfRank (pullbackModule f E) r :=
  LeBrunSalamon.PublishedInputs.SheafFunctoriality.pullback_locallyFree f hE

def trivialLine (X : Scheme) : LineBundle X :=
  ⟨structureModule X, structureModule_rank X⟩

def tensorLine {X : Scheme} (L M : LineBundle X) : LineBundle X where
  sheaf := tensorSheaf L.sheaf M.sheaf
  locallyFree := by
    simpa using tensorSheaf_locallyFree L.locallyFree M.locallyFree

def dualLine {X : Scheme} (L : LineBundle X) : LineBundle X :=
  ⟨dualSheaf L.sheaf, dualSheaf_locallyFree L.locallyFree⟩

def pullbackLine {X Y : Scheme} (f : X ⟶ Y) (L : LineBundle Y) :
    LineBundle X :=
  ⟨pullbackModule f L.sheaf, pullback_locallyFree f L.locallyFree⟩

/-- Nonnegative tensor powers, with an explicit zeroth power O_X. -/
def linePower {X : Scheme} (L : LineBundle X) : ℕ → LineBundle X
  | 0 => trivialLine X
  | k + 1 => tensorLine (linePower L k) L

/-- Negative powers mean positive powers of the actual dual line. -/
def linePowerInt {X : Scheme} (L : LineBundle X) : ℤ → LineBundle X
  | Int.ofNat k => linePower L k
  | Int.negSucc k => linePower (dualLine L) (k + 1)

end LeBrunSalamon.PhaseTwentySix

/- Insert at the root namespace after the checked Hom/unit/local-isomorphism infrastructure.
Each component below closes its own noncomputable section; the Generic open cannot leak.
Copied standalone contexts and the original target wrapper are omitted. -/

/- Checked component: tensor_sheafification_naturality.lean; opens and variables are local to this section. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory

namespace LeBrunSalamon.SheafTensor

variable {C : Type} [Category.{0} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat}
variable [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]

theorem sheafificationHomEquiv_comp
    {P : PresheafOfModules R.obj} {F G : SheafOfModules R}
    (f : (PresheafOfModules.sheafification (𝟙 R.obj)).obj P ⟶ F) (g : F ⟶ G) :
    (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) (P := P) (F := G)) (f ≫ g) =
      (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) (P := P) (F := F)) f ≫ g.val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv_naturality_right f g

theorem sheafificationHomEquiv_unit
    {P : PresheafOfModules R.obj} {F : SheafOfModules R}
    (f : (PresheafOfModules.sheafification (𝟙 R.obj)).obj P ⟶ F) :
    (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) (P := P) (F := F)) f =
      (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P ≫ f.val := rfl

theorem sheafificationUnit_lift
    {P : PresheafOfModules R.obj} {F : SheafOfModules R} (h : P ⟶ F.val) :
    (PresheafOfModules.sheafificationAdjunction (R := R) (𝟙 R.obj)).unit.app P ≫
      ((PresheafOfModules.sheafificationHomEquiv (R := R) (𝟙 R.obj)
        (P := P) (F := F)).symm h).val = h :=
  (sheafificationHomEquiv_unit (R := R) (P := P) (F := F)
    ((PresheafOfModules.sheafificationHomEquiv (R := R) (𝟙 R.obj)
      (P := P) (F := F)).symm h)).symm.trans
        ((PresheafOfModules.sheafificationHomEquiv (R := R) (𝟙 R.obj)
          (P := P) (F := F)).apply_symm_apply h)

theorem sheafificationLift_comp
    {P : PresheafOfModules R.obj} {F G : SheafOfModules R}
    (h : P ⟶ F.val) (g : F ⟶ G) :
    (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)
      (P := P) (F := F)).symm h ≫ g =
        (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)
          (P := P) (F := G)).symm (h ≫ g.val) := by
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)
    (P := P) (F := G)).injective
  have hn := sheafificationHomEquiv_comp (R := R) (P := P) (F := F) (G := G)
    ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)
      (P := P) (F := F)).symm h) g
  have hu := (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)
    (P := P) (F := F)).apply_symm_apply h
  have hv := (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)
    (P := P) (F := G)).apply_symm_apply (h ≫ g.val)
  exact hn.trans ((congrArg (fun k : P ⟶ F.val => k ≫ g.val) hu).trans hv.symm)

theorem sheafMap_over_val (U : C) {E F : SheafOfModules R} (f : E ⟶ F) :
    (f.over U).val = (PresheafOfModules.pushforward₀ (Over.forget U) R.obj).map f.val := rfl

end LeBrunSalamon.SheafTensor

end -- component noncomputable section

/- Checked component: tensor_lift_over.lean; opens and variables are local to this section. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne

namespace LeBrunSalamon.SheafTensor

set_option maxHeartbeats 1000000 in
/-- A sheafification lift restricts to the lift of the restricted map.
The explicit unit factorization keeps the lift symbolic in this compatibility statement. -/
theorem sheafificationLift_over {X : Scheme} (U : X.Opens)
    {P : PresheafOfModules X.ringCatSheaf.obj} {F : OModule X}
    (l : (PresheafOfModules.sheafification (C := X.Opens)
        (J := Opens.grothendieckTopology X) (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).obj P ⟶ F)
    (h : P ⟶ F.val)
    (hl : (PresheafOfModules.sheafificationAdjunction (C := X.Opens)
        (J := Opens.grothendieckTopology X) (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).unit.app P ≫
      l.val = h) :
    sheafificationOverHom X U P ≫ l.over U =
      (PresheafOfModules.sheafificationHomEquiv (C := Over U)
        (J := (Opens.grothendieckTopology X).over U) (R := X.ringCatSheaf.over U)
        (𝟙 (X.ringCatSheaf.over U).obj)
        (P := (overPresheaf X U).obj P) (F := F.over U)).symm
          ((overPresheaf X U).map h) := by
  let η := (PresheafOfModules.sheafificationAdjunction (C := X.Opens)
        (J := Opens.grothendieckTopology X) (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).unit.app P
  let sfU := PresheafOfModules.sheafificationHomEquiv (C := Over U)
        (J := (Opens.grothendieckTopology X).over U) (R := X.ringCatSheaf.over U)
    (𝟙 (X.ringCatSheaf.over U).obj)
    (P := (overPresheaf X U).obj P) (F := F.over U)
  have hn : sheafificationOverHom X U P ≫ l.over U =
      sfU.symm ((overPresheaf X U).map η ≫ (l.over U).val) :=
    sheafificationLift_comp (C := Over U)
      (J := (Opens.grothendieckTopology X).over U) (R := X.ringCatSheaf.over U)
      (P := (overPresheaf X U).obj P)
      (F := ((PresheafOfModules.sheafification (C := X.Opens)
        (J := Opens.grothendieckTopology X) (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).obj P).over U)
      (G := F.over U) ((overPresheaf X U).map η) (l.over U)
  have hm : (overPresheaf X U).map η ≫ (l.over U).val = (overPresheaf X U).map h :=
    (congrArg (fun k :
        (((PresheafOfModules.sheafification (C := X.Opens)
        (J := Opens.grothendieckTopology X) (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).obj P).over U).val ⟶
          (F.over U).val => (overPresheaf X U).map η ≫ k)
      (sheafMap_over_val (C := X.Opens) (J := Opens.grothendieckTopology X) (R := X.ringCatSheaf) U l)).trans
        (((overPresheaf X U).map_comp η l.val).symm.trans
          (congrArg (fun k : P ⟶ F.val => (overPresheaf X U).map k) hl))
  exact hn.trans (congrArg sfU.symm hm)

end LeBrunSalamon.SheafTensor

end -- component noncomputable section

/- Checked component: tensor_line_evaluation_generic.lean; opens and variables are local to this section. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Opposite
open LeBrunSalamon.PhaseTwentyFive.HomConstruction.Generic

namespace LeBrunSalamon.SheafTensor.LocalEvaluation

variable {C : Type} [Category.{0} C] {J : GrothendieckTopology C}
variable {R : Sheaf J CommRingCat}

/-- The actual local-Hom evaluation, before sheafifying the tensor product. -/
def evaluationPresheaf (E F : Modules R) :
    tensorPresheaf R (object E F) E ⟶ F.val :=
  PresheafOfModulesOfCommRing.homMk
    (fun U => ModuleCat.ofHom (TensorProduct.lift (evaluationAt E F U.unop)))
    (fun i => ModuleCat.MonoidalCategory.tensor_ext (fun φ e =>
      (evaluationAt_naturality i.unop φ e).symm))

theorem evaluationPresheaf_mapIso {E E' : Modules R} (e : E ≅ E') (F : Modules R) :
    PresheafOfModulesOfCommRing.Monoidal.tensorHom
        ((mapIso e (Iso.refl F)).hom.val) e.hom.val ≫ evaluationPresheaf E' F =
      evaluationPresheaf E F := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext (R := R.obj.obj U)
  intro φ x
  change φ.app (op (Over.mk (𝟙 U.unop)))
      (e.inv.val.app U (e.hom.val.app U x)) =
    φ.app (op (Over.mk (𝟙 U.unop))) x
  exact congrArg (fun y => φ.app (op (Over.mk (𝟙 U.unop))) y)
    (congrArg (fun k : E ⟶ E => k.val.app U x) e.hom_inv_id)

theorem evaluationPresheaf_unit (F : Modules R) :
    evaluationPresheaf (SheafOfModules.unit (ringSheaf R)) F =
      PresheafOfModulesOfCommRing.Monoidal.tensorHom
          (unitSourceIso F).hom.val (𝟙 (SheafOfModules.unit (ringSheaf R)).val) ≫
        (CategoryTheory.MonoidalCategory.rightUnitor
          (C := PresheafOfModulesOfCommRing R.obj) F.val).hom := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext (R := R.obj.obj U)
  intro φ r
  let a : RingSections R U.unop := r
  let fφ : RingSections R U.unop →ₗ[RingSections R U.unop] SectionsOn F U.unop :=
    (φ.app (op (Over.mk (𝟙 U.unop)))).hom
  change fφ a = a • fφ (1 : RingSections R U.unop)
  exact (congrArg fφ (mul_one a).symm).trans (fφ.map_smul a 1)

instance evaluationPresheaf_unit_isIso (F : Modules R) :
    IsIso (evaluationPresheaf (SheafOfModules.unit (ringSheaf R)) F) := by
  rw [evaluationPresheaf_unit]
  change IsIso ((CategoryTheory.MonoidalCategory.tensorIso
    (C := PresheafOfModulesOfCommRing R.obj)
    ((SheafOfModules.forget (ringSheaf R)).mapIso (unitSourceIso F)) (Iso.refl _) ≪≫
      CategoryTheory.MonoidalCategory.rightUnitor
        (C := PresheafOfModulesOfCommRing R.obj) F.val).hom)
  infer_instance

/-- A sheaf isomorphic to the unit has invertible tensor evaluation. -/
theorem evaluationPresheaf_isIso_of_unit {E : Modules R} (F : Modules R)
    (e : E ≅ SheafOfModules.unit (ringSheaf R)) : IsIso (evaluationPresheaf E F) := by
  rw [← evaluationPresheaf_mapIso e F]
  let t := CategoryTheory.MonoidalCategory.tensorIso
    (C := PresheafOfModulesOfCommRing R.obj)
    ((SheafOfModules.forget (ringSheaf R)).mapIso (mapIso e (Iso.refl F)))
    ((SheafOfModules.forget (ringSheaf R)).mapIso e)
  change IsIso (t.hom ≫ evaluationPresheaf (SheafOfModules.unit (ringSheaf R)) F)
  infer_instance

variable [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]

/-- An invertible presheaf map into a sheaf remains invertible after taking its sheafification lift. -/
theorem sheafificationLift_isIso {P : PresheafOfModules (ringSheaf R).obj}
    {F : Modules R} (f : P ⟶ F.val) [IsIso f] :
    IsIso ((PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf R).obj)).symm f) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)
  have heq : (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf R).obj)).symm f =
      (PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).map f ≫ adj.counit.app F := by
    apply (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf R).obj)).injective
    rw [Equiv.apply_symm_apply]
    exact ((adj.homEquiv P F).apply_symm_apply f).symm
  rw [heq]
  infer_instance

/-- Evaluation for the genuine sheafified tensor and the actual local Hom sheaf. -/
def evaluation (E F : Modules R) : tensor R (object E F) E ⟶ F :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf R).obj)).symm
    (evaluationPresheaf E F)

theorem evaluation_isIso_of_unit {E : Modules R} (F : Modules R)
    (e : E ≅ SheafOfModules.unit (ringSheaf R)) : IsIso (evaluation E F) := by
  letI := evaluationPresheaf_isIso_of_unit F e
  exact sheafificationLift_isIso (evaluationPresheaf E F)

end LeBrunSalamon.SheafTensor.LocalEvaluation

end -- component noncomputable section

/- Checked component: tensor_line_evaluation.lean; opens and variables are local to this section. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwentyFive

namespace LeBrunSalamon.SheafTensor

namespace LocalEvaluation

/-- The presheaf evaluation comparison on a slice is computed by actual iterated slices. -/
theorem evaluationPresheaf_over {X : Scheme} (U : X.Opens) (E F : OModule X) :
    (overPresheaf X U).map (evaluationPresheaf (R := X.sheaf) E F) =
      (overTensorPresheafIso U (HomConstruction.Generic.object (R := X.sheaf) E F) E).hom ≫
        PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := (X.sheaf.over U).obj)
          (HomConstruction.Generic.overIso (R := X.sheaf) E F U).hom.val
          (𝟙 (E.over U).val) ≫
            evaluationPresheaf (R := X.sheaf.over U) (E.over U) (F.over U) := by
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.MonoidalCategory.tensor_ext (R := X.presheaf.obj (op V.unop.left))
  intro φ e
  rfl

theorem evaluationPresheaf_over_isIso_of_unit {X : Scheme} (U : X.Opens)
    (E F : OModule X)
    (e : E.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    IsIso ((overPresheaf X U).map (evaluationPresheaf (R := X.sheaf) E F)) := by
  letI := evaluationPresheaf_isIso_of_unit (R := X.sheaf.over U) (F.over U) e
  let t := CategoryTheory.MonoidalCategory.tensorIso
    (C := PresheafOfModulesOfCommRing (X.sheaf.over U).obj)
    ((SheafOfModules.forget (X.ringCatSheaf.over U)).mapIso
      (HomConstruction.Generic.overIso (R := X.sheaf) E F U))
    (Iso.refl (E.over U).val)
  have ht : IsIso
      ((overTensorPresheafIso U (HomConstruction.Generic.object (R := X.sheaf) E F) E).hom ≫
        t.hom ≫ evaluationPresheaf (R := X.sheaf.over U) (E.over U) (F.over U)) :=
    inferInstance
  exact (evaluationPresheaf_over U E F).symm ▸ ht

set_option maxHeartbeats 1000000 in
theorem evaluation_over_isIso_of_unit {X : Scheme} (U : X.Opens) (E F : OModule X)
    (e : E.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    IsIso ((evaluation (R := X.sheaf) E F).over U) := by
  letI := evaluationPresheaf_over_isIso_of_unit U E F e
  letI : IsIso ((PresheafOfModules.sheafificationHomEquiv (C := Over U)
      (J := (Opens.grothendieckTopology X).over U) (R := X.ringCatSheaf.over U)
      (𝟙 (X.ringCatSheaf.over U).obj)
      (P := (overPresheaf X U).obj
        (tensorPresheaf X.sheaf (HomConstruction.Generic.object (R := X.sheaf) E F) E))
      (F := F.over U)).symm
        ((overPresheaf X U).map (evaluationPresheaf (R := X.sheaf) E F))) :=
    sheafificationLift_isIso (R := X.sheaf.over U) (F := F.over U)
      ((overPresheaf X U).map (evaluationPresheaf (R := X.sheaf) E F))
  have hl : (PresheafOfModules.sheafificationAdjunction
      (C := X.Opens) (J := Opens.grothendieckTopology X) (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).unit.app
        (tensorPresheaf X.sheaf (HomConstruction.Generic.object (R := X.sheaf) E F) E) ≫
          (evaluation (R := X.sheaf) E F).val = evaluationPresheaf (R := X.sheaf) E F :=
    sheafificationUnit_lift (C := X.Opens) (J := Opens.grothendieckTopology X)
      (R := X.ringCatSheaf)
      (P := tensorPresheaf X.sheaf (HomConstruction.Generic.object (R := X.sheaf) E F) E)
      (F := F) (evaluationPresheaf (R := X.sheaf) E F)
  exact IsIso.of_isIso_fac_left (sheafificationLift_over (X := X) U
    (P := tensorPresheaf X.sheaf (HomConstruction.Generic.object (R := X.sheaf) E F) E)
    (F := F) (evaluation (R := X.sheaf) E F) (evaluationPresheaf (R := X.sheaf) E F) hl)

/-- Evaluation against an invertible sheaf is an isomorphism for every target sheaf. -/
theorem evaluation_isIso_of_rank_one {X : Scheme} {E : OModule X}
    (F : OModule X) (hE : IsLocallyFreeOfRank E 1) :
    IsIso (evaluation (R := X.sheaf) E F) := by
  obtain ⟨q, hq, hr⟩ := hE
  letI := hq
  apply SheafModuleLocal.isIso_of_coversTop q.coversTop (evaluation (R := X.sheaf) E F)
  intro i
  exact evaluation_over_isIso_of_unit (q.X i) E F
    ((localBasisTrivialization q hr i).symm ≪≫
      coproductUniqueIso (fun _ : Fin 1 => SheafOfModules.unit (X.ringCatSheaf.over (q.X i))))

theorem evaluation_pair {X : Scheme} (E F : OModule X) (U : X.Opens)
    (φ : SectionsOn (HomConstruction.Generic.object (R := X.sheaf) E F) U)
    (e : SectionsOn E U) :
    (evaluation (R := X.sheaf) E F).val.app (op U)
      ((tensorPresentation (HomConstruction.Generic.object (R := X.sheaf) E F) E).pair.apply U φ e) =
        HomConstruction.Generic.evaluationAt (R := X.sheaf) E F U φ e := by
  have h := (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)
    (P := tensorPresheaf X.sheaf (HomConstruction.Generic.object (R := X.sheaf) E F) E)
    (F := F)).apply_symm_apply
    (evaluationPresheaf (R := X.sheaf) E F)
  exact congrArg (fun k : tensorPresheaf X.sheaf
      (HomConstruction.Generic.object (R := X.sheaf) E F) E ⟶ F.val =>
        k.app (op U) (φ ⊗ₜ[RingSections X U] e)) h

/-- The evaluation supplied by the original chosen Hom agrees with concrete local evaluation. -/
theorem chosen_evaluation_eq {X : Scheme} (E F : OModule X) :
    tensorMap (internalHomGenericIso E F).hom (𝟙 E) ≫ evaluation (R := X.sheaf) E F =
      (internalHomPresentation E F).evaluate := by
  apply ((tensorPresentation (internalHomSheaf E F) E).universal F).1
  apply sheafBilinearMap_ext
  intro U φ e
  change (evaluation (R := X.sheaf) E F).val.app (op U)
      ((tensorMap (internalHomGenericIso E F).hom (𝟙 E)).app U
        ((tensorPresentation (internalHomSheaf E F) E).pair.apply U φ e)) = _
  exact (congrArg (fun z => (evaluation (R := X.sheaf) E F).val.app (op U) z)
    (tensorMap_apply (internalHomGenericIso E F).hom (𝟙 E) U φ e)).trans
      ((evaluation_pair E F U ((internalHomGenericIso E F).hom.app U φ) e).trans
        (internalHomGenericIso_evaluate_pair E F U φ e))

theorem chosen_evaluation_isIso_of_rank_one {X : Scheme} {E : OModule X}
    (F : OModule X) (hE : IsLocallyFreeOfRank E 1) :
    IsIso (internalHomPresentation E F).evaluate := by
  letI := evaluation_isIso_of_rank_one F hE
  let t := PhaseTwentyFive.tensorIso (internalHomGenericIso E F) (Iso.refl E)
  have ht : IsIso (t.hom ≫ evaluation (R := X.sheaf) E F) := inferInstance
  exact (chosen_evaluation_eq E F) ▸ ht

end LocalEvaluation
end LeBrunSalamon.SheafTensor

end -- component noncomputable section


namespace LeBrunSalamon.PhaseTwentySix
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive

set_option backward.isDefEq.respectTransparency false in
theorem line_dual_evaluation {X : Scheme} (L : LineBundle X) :
    Nonempty ((tensorLine (dualLine L) L).sheaf ≅ (trivialLine X).sheaf) := by
  letI := SheafTensor.LocalEvaluation.chosen_evaluation_isIso_of_rank_one
    (structureModule X) L.locallyFree
  exact ⟨asIso (internalHomPresentation L.sheaf (structureModule X)).evaluate⟩

end LeBrunSalamon.PhaseTwentySix

namespace LeBrunSalamon.SheafTensor
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwentyFive
set_option backward.isDefEq.respectTransparency false

section

/-- Tensor powers of actual module sheaves, with zeroth power the structure module. -/
def tensorPower {X : Scheme} (E : OModule X) : ℕ → OModule X
  | 0 => structureModule X
  | n + 1 => tensorSheaf (tensorPower E n) E

/-- Isomorphic sheaves have isomorphic powers, with the same recursive convention. -/
def tensorPowerCongrIso {X : Scheme} {E F : OModule X} (e : E ≅ F) :
    ∀ n : ℕ, tensorPower E n ≅ tensorPower F n
  | 0 => Iso.refl _
  | n + 1 => PhaseTwentyFive.tensorIso (tensorPowerCongrIso e n) e

def tensorPowerOneIso {X : Scheme} (E : OModule X) : tensorPower E 1 ≅ E :=
  TensorConstruction.leftUnitIso E

/-- Splitting a nonnegative tensor power into two powers, using the actual associator. -/
def tensorPowerAddIso {X : Scheme} (E : OModule X) (a b : ℕ) :
    tensorPower E (a + b) ≅ tensorSheaf (tensorPower E a) (tensorPower E b) := by
  induction b with
  | zero =>
      simpa only [Nat.add_zero, tensorPower] using
        (TensorConstruction.commIso (tensorPower E a) (structureModule X) ≪≫
          TensorConstruction.leftUnitIso (tensorPower E a)).symm
  | succ b ih =>
      change tensorSheaf (tensorPower E (a + b)) E ≅
        tensorSheaf (tensorPower E a) (tensorSheaf (tensorPower E b) E)
      exact PhaseTwentyFive.tensorIso ih (Iso.refl E) ≪≫
        associativityIso (tensorPower E a) (tensorPower E b) E

/-- Iterating tensor powers multiplies their nonnegative exponents. -/
def tensorPowerMulIso {X : Scheme} (E : OModule X) (a b : ℕ) :
    tensorPower (tensorPower E a) b ≅ tensorPower E (a * b) := by
  induction b with
  | zero =>
      simpa only [Nat.mul_zero, tensorPower] using Iso.refl (structureModule X)
  | succ b ih =>
      simpa only [Nat.mul_succ, tensorPower] using
        PhaseTwentyFive.tensorIso ih (Iso.refl (tensorPower E a)) ≪≫
          (tensorPowerAddIso E (a * b) a).symm

end

end LeBrunSalamon.SheafTensor

namespace LeBrunSalamon.PhaseTwentySix
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive

theorem linePower_sheaf_eq_tensorPower {X : Scheme} (L : LineBundle X) (n : ℕ) :
    (linePower L n).sheaf = SheafTensor.tensorPower L.sheaf n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change tensorSheaf (linePower L n).sheaf L.sheaf =
        tensorSheaf (SheafTensor.tensorPower L.sheaf n) L.sheaf
      rw [ih]

theorem linePower_add {X : Scheme} (L : LineBundle X) (a b : ℕ) :
    Nonempty ((linePower L (a + b)).sheaf ≅
      (tensorLine (linePower L a) (linePower L b)).sheaf) := by
  change Nonempty ((linePower L (a + b)).sheaf ≅
    tensorSheaf (linePower L a).sheaf (linePower L b).sheaf)
  simpa only [linePower_sheaf_eq_tensorPower] using
    (⟨SheafTensor.tensorPowerAddIso L.sheaf a b⟩ :
      Nonempty (SheafTensor.tensorPower L.sheaf (a + b) ≅
        tensorSheaf (SheafTensor.tensorPower L.sheaf a) (SheafTensor.tensorPower L.sheaf b)))

theorem linePower_mul {X : Scheme} (L : LineBundle X) (a b : ℕ) :
    Nonempty ((linePower (linePower L a) b).sheaf ≅
      (linePower L (a * b)).sheaf) := by
  simpa only [linePower_sheaf_eq_tensorPower] using
    (⟨SheafTensor.tensorPowerMulIso L.sheaf a b⟩ :
      Nonempty (SheafTensor.tensorPower (SheafTensor.tensorPower L.sheaf a) b ≅
        SheafTensor.tensorPower L.sheaf (a * b)))

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix

namespace LinePowerPullbackProof

theorem linePower_pullback {X Y : Scheme} (f : X ⟶ Y)
    (L : LineBundle Y) (k : ℕ) :
    Nonempty ((pullbackLine f (linePower L k)).sheaf ≅
      (linePower (pullbackLine f L) k).sheaf) := by
  induction k with
  | zero =>
      change Nonempty (pullbackModule f (structureModule Y) ≅ structureModule X)
      let : (TopologicalSpace.Opens.map f.base).Final := inferInstance
      let m : pullbackModule f (structureModule Y) ⟶ structureModule X :=
        SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom
      have : IsIso m := by
        dsimp [m]
        exact inferInstanceAs (IsIso (SheafOfModules.pullbackObjUnitToUnit
          (F := TopologicalSpace.Opens.map f.base) f.toRingCatSheafHom))
      exact ⟨asIso m⟩
  | succ k ih =>
      obtain ⟨e⟩ := ih
      change Nonempty (pullbackModule f
        (tensorSheaf (linePower L k).sheaf L.sheaf) ≅
          tensorSheaf (linePower (pullbackLine f L) k).sheaf
            (pullbackModule f L.sheaf))
      obtain ⟨t⟩ := tensorSheaf_pullback f (linePower L k).sheaf L.sheaf
      exact ⟨t ≪≫ tensorIso e (Iso.refl (pullbackModule f L.sheaf))⟩

end LinePowerPullbackProof

end

theorem linePower_pullback {X Y : Scheme} (f : X ⟶ Y)
    (L : LineBundle Y) (k : ℕ) :
    Nonempty ((pullbackLine f (linePower L k)).sheaf ≅
      (linePower (pullbackLine f L) k).sheaf) := by
  exact LeBrunSalamon.PhaseTwentySix.LinePowerPullbackProof.linePower_pullback (X := X) (Y := Y) (f := f) (L := L) (k := k)

def determinantLine {X : Scheme} {r : ℕ} (E : AlgebraicVectorBundle X r) :
    LineBundle X where
  sheaf := exteriorSheaf E.sheaf r
  locallyFree := by
    simpa using exteriorSheaf_locallyFree E.locallyFree r

def canonicalLine {d : ℕ} (X : SmoothProperComplexVariety d) :
    LineBundle X.scheme := determinantLine (intrinsicCotangentBundle X)

def anticanonicalLine {d : ℕ} (X : SmoothProperComplexVariety d) :
    LineBundle X.scheme := dualLine (canonicalLine X)

end LeBrunSalamon.PhaseTwentySix

/- The determinant-duality specialization below is proved from Stacks Project,
Lemma 48.29.1 (Tag 0E9Y), stated for ordinary locally ringed spaces:
https://stacks.math.columbia.edu/tag/0E9Y . The generic input gives the
exterior-power map for an exact sequence and its invertibility when the
quotient is locally free of the difference rank. The identity sequence,
rank-zero quotient, tensor cancellation, and intrinsic specialization are
proved here. -/
section TangentDeterminantProofSection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix

namespace LeBrunSalamon.PublishedInputs.Determinant

/-- The globally locally-free case of the canonical map and invertibility
criterion in Stacks Project, Lemma 48.29.1 (Tag 0E9Y). All objects are genuine
module sheaves, and the conclusion provides a morphism with `IsIso`.
The rank inequality avoids the source's negative-exterior-degree convention. -/
theorem lciExteriorMap_isIso {X : Scheme} {r₁ r₀ : ℕ}
    (E₁ : AlgebraicVectorBundle X r₁) (E₀ : AlgebraicVectorBundle X r₀)
    (F : OModule X) (α : E₁.sheaf ⟶ E₀.sheaf) (β : E₀.sheaf ⟶ F)
    (hcomp : α ≫ β = 0)
    (hseq : (ShortComplex.mk α β hcomp).ShortExact)
    (hrank : r₁ ≤ r₀) (hF : IsLocallyFreeOfRank F (r₀ - r₁)) :
    ∃ δ : exteriorSheaf F (r₀ - r₁) ⟶
        tensorSheaf (exteriorSheaf (dualSheaf E₁.sheaf) r₁)
          (exteriorSheaf E₀.sheaf r₀), IsIso δ := by
  sorry

end LeBrunSalamon.PublishedInputs.Determinant

namespace LeBrunSalamon.TangentDeterminantProof

/-- A concrete free sheaf on the empty basis, with the genuine rank-zero proof. -/
def zeroRankBundle (X : Scheme) : AlgebraicVectorBundle X 0 :=
  ⟨SheafOfModules.free (R := X.ringCatSheaf) (Fin 0), freeSheaf_rank X 0⟩

theorem zeroRankBundle_isZero (X : Scheme) :
    IsZero (zeroRankBundle X).sheaf := by
  rw [IsZero.iff_id_eq_zero]
  apply (SheafOfModules.freeHomEquiv (zeroRankBundle X).sheaf).injective
  funext i
  exact Fin.elim0 i

/-- The identity followed by the map to the actual zero-rank sheaf is short exact. -/
theorem identityZero_shortExact {X : Scheme} (E : OModule X) :
    (ShortComplex.mk (𝟙 E) (0 : E ⟶ (zeroRankBundle X).sheaf)
      (by simp)).ShortExact := by
  letI : Epi (0 : E ⟶ (zeroRankBundle X).sheaf) := by
    constructor
    intro W f g _
    exact (zeroRankBundle_isZero X).eq_of_src f g
  refine { exact := ?_, mono_f := inferInstance, epi_g := inferInstance }
  exact (ShortComplex.exact_iff_epi _ rfl).2 inferInstance

/-- The identity sequence gives a tensor inverse for the top exterior power. -/
theorem exteriorDual_tensor_exterior {X : Scheme} {r : ℕ}
    (E : AlgebraicVectorBundle X r) :
    Nonempty (tensorSheaf (exteriorSheaf (dualSheaf E.sheaf) r)
      (exteriorSheaf E.sheaf r) ≅ structureModule X) := by
  have hF : IsLocallyFreeOfRank (zeroRankBundle X).sheaf (r - r) := by
    simpa only [Nat.sub_self] using (zeroRankBundle X).locallyFree
  obtain ⟨δ, hδ⟩ := PublishedInputs.Determinant.lciExteriorMap_isIso
    E E (zeroRankBundle X).sheaf (𝟙 E.sheaf) 0 (by simp)
    (identityZero_shortExact E.sheaf) (Nat.le_refl r) hF
  letI := hδ
  let e : exteriorSheaf (zeroRankBundle X).sheaf 0 ≅
      tensorSheaf (exteriorSheaf (dualSheaf E.sheaf) r)
        (exteriorSheaf E.sheaf r) := by
    simpa only [Nat.sub_self] using asIso δ
  obtain ⟨z⟩ := exteriorSheaf_zero (zeroRankBundle X).sheaf
  exact ⟨e.symm ≪≫ z⟩

/-- Tensor inverses of an invertible sheaf agree with its actual internal dual. -/
theorem inverse_iso_dual {X : Scheme} (L : LineBundle X) (D : OModule X)
    (h : Nonempty (tensorSheaf D L.sheaf ≅ structureModule X)) :
    Nonempty (D ≅ dualSheaf L.sheaf) := by
  obtain ⟨q⟩ := h
  obtain ⟨ev⟩ := line_dual_evaluation L
  let P := dualSheaf L.sheaf
  let A := L.sheaf
  exact ⟨(TensorConstruction.leftUnitIso D).symm ≪≫
    tensorIso ev.symm (Iso.refl D) ≪≫
    SheafTensor.associativityIso P A D ≪≫
    tensorIso (Iso.refl P) (TensorConstruction.commIso A D) ≪≫
    tensorIso (Iso.refl P) q ≪≫ TensorConstruction.rightUnitIso P⟩

/-- Determinant duality for every finite locally free sheaf on every scheme. -/
theorem determinantDual_iso {X : Scheme} {r : ℕ}
    (E : AlgebraicVectorBundle X r) :
    Nonempty (exteriorSheaf (dualSheaf E.sheaf) r ≅
      dualSheaf (exteriorSheaf E.sheaf r)) := by
  exact inverse_iso_dual (determinantLine E)
    (exteriorSheaf (dualSheaf E.sheaf) r) (exteriorDual_tensor_exterior E)

/-- The requested intrinsic statement is the cotangent-bundle specialization. -/
theorem tangentDeterminant_anticanonical {d : ℕ}
    (X : SmoothProperComplexVariety d) :
    Nonempty ((determinantLine (intrinsicTangentBundle X)).sheaf ≅
      (anticanonicalLine X).sheaf) := by
  exact determinantDual_iso (intrinsicCotangentBundle X)

/-- Cancel the dual determinant in the generic fundamental exterior map. -/
theorem determinant_shortExact {X : Scheme} {a b : ℕ}
    (E : AlgebraicVectorBundle X a) (F : AlgebraicVectorBundle X (a + b))
    (G : AlgebraicVectorBundle X b)
    (i : E.sheaf ⟶ F.sheaf) (p : F.sheaf ⟶ G.sheaf)
    (hz : i ≫ p = 0) (hex : (ShortComplex.mk i p hz).ShortExact) :
    Nonempty ((determinantLine F).sheaf ≅
      (tensorLine (determinantLine E) (determinantLine G)).sheaf) := by
  have hG : IsLocallyFreeOfRank G.sheaf (a + b - a) := by
    simpa only [Nat.add_sub_cancel_left] using G.locallyFree
  obtain ⟨δ, hδ⟩ := PublishedInputs.Determinant.lciExteriorMap_isIso
    E F G.sheaf i p hz hex (Nat.le_add_right a b) hG
  letI := hδ
  obtain ⟨d⟩ := determinantDual_iso E
  let e₀ : (determinantLine G).sheaf ≅
      tensorSheaf (exteriorSheaf (dualSheaf E.sheaf) a)
        (determinantLine F).sheaf := by
    simpa only [determinantLine, Nat.add_sub_cancel_left] using asIso δ
  let e := e₀ ≪≫ tensorIso d (Iso.refl (determinantLine F).sheaf)
  obtain ⟨ev⟩ := line_dual_evaluation (determinantLine E)
  let A := (determinantLine E).sheaf
  let B := (determinantLine F).sheaf
  let D := dualSheaf A
  exact ⟨(TensorConstruction.leftUnitIso B).symm ≪≫
    tensorIso ev.symm (Iso.refl B) ≪≫
    tensorIso (TensorConstruction.commIso D A) (Iso.refl B) ≪≫
    SheafTensor.associativityIso A D B ≪≫
    tensorIso (Iso.refl A) e.symm⟩

end LeBrunSalamon.TangentDeterminantProof

end TangentDeterminantProofSection

namespace LeBrunSalamon.PhaseTwentySix
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive

theorem _root_.LeBrunSalamon.PublishedInputs.Step3e.tangentDeterminant_anticanonical
    {d : ℕ} (X : SmoothProperComplexVariety d) :
    Nonempty ((determinantLine (intrinsicTangentBundle X)).sheaf ≅
      (anticanonicalLine X).sheaf) := by
  exact LeBrunSalamon.TangentDeterminantProof.tangentDeterminant_anticanonical X

/-- Project-facing form of `det(Eᵛ) ≅ det(E)ᵛ` for the intrinsic tangent and
cotangent bundles. -/
theorem tangentDeterminant_anticanonical {d : ℕ}
    (X : SmoothProperComplexVariety d) :
    Nonempty ((determinantLine (intrinsicTangentBundle X)).sheaf ≅
      (anticanonicalLine X).sheaf) := by
  exact LeBrunSalamon.PublishedInputs.Step3e.tangentDeterminant_anticanonical X

/-- The nonvanishing open of a line-bundle section is the union of opens where the section is an
isomorphism O_U ≅ L|_U. The source of `restrictSection` is f*O_X; being an isomorphism is unaffected by
the canonical identification f*O_X ≅ O_U. -/
def nonvanishingOpen {X : Scheme} (L : LineBundle X)
    (s : AlgebraicSection L.sheaf) : X.Opens :=
  sSup {U : X.Opens | IsIso (restrictSection U.ι s)}

/-- Intrinsic ampleness, using the affine-nonvanishing definition.
Quasi-compactness is part of this convention (Stacks Tag 01PR). -/
def IsAmpleLine {X : Scheme} (L : LineBundle X) : Prop :=
  CompactSpace X ∧ ∀ x : X,
    ∃ (m : ℕ) (_ : 0 < m)
      (s : AlgebraicSection (linePower L m).sheaf),
      x ∈ nonvanishingOpen (linePower L m) s ∧
      IsAffineOpen (nonvanishingOpen (linePower L m) s)

def IsFano {d : ℕ} (X : SmoothProperComplexVariety d) : Prop :=
  IsAmpleLine (anticanonicalLine X)

/- Source-only Phase 3 integration: nonvanishing_locus. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseTwentyFive

namespace NonvanishingLocusProof

def moduleStalk (X : Scheme) (x : X) : X.Modules ⥤ AddCommGrpCat :=
  Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat x

theorem isIso_iff_stalk {X : Scheme} {E F : X.Modules} (f : E ⟶ F) :
    IsIso f ↔ ∀ x : X, IsIso ((moduleStalk X x).map f) := by
  constructor
  · intro hf x
    letI := hf
    infer_instance
  · intro h
    let T := SheafOfModules.toSheaf X.ringCatSheaf
    letI : IsIso (T.map f) :=
      (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso (T.map f)).mpr h
    letI : IsIso ((Scheme.Modules.toPresheaf X).map f) :=
      (TopCat.Sheaf.forget AddCommGrpCat X).map_isIso (T.map f)
    exact isIso_of_reflects_iso f (Scheme.Modules.toPresheaf X)

theorem isIso_pullback_open_iff {X : Scheme} (U : X.Opens)
    {E F : X.Modules} (f : E ⟶ F) :
    IsIso ((Scheme.Modules.pullback U.ι).map f) ↔
      ∀ x : U, IsIso ((moduleStalk X x.val).map f) := by
  constructor
  · intro hf x
    have hres : IsIso ((Scheme.Modules.restrictFunctor U.ι).map f) :=
      (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback U.ι) f).mpr hf
    have hx := (isIso_iff_stalk ((Scheme.Modules.restrictFunctor U.ι).map f)).mp hres x
    exact (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso U.ι x) f).mp hx
  · intro h
    apply (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback U.ι) f).mp
    apply (isIso_iff_stalk ((Scheme.Modules.restrictFunctor U.ι).map f)).mpr
    intro x
    exact (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso U.ι x) f).mpr (h x)

theorem nonvanishingOpen_isIso {X : Scheme} (L : LineBundle X)
    (s : AlgebraicSection L.sheaf) :
    IsIso (restrictSection (nonvanishingOpen L s).ι s) := by
  apply (isIso_pullback_open_iff (nonvanishingOpen L s) s).mpr
  intro x
  obtain ⟨U, hU, hx⟩ := TopologicalSpace.Opens.mem_sSup.mp x.property
  exact (isIso_pullback_open_iff U s).mp hU ⟨x.val, hx⟩

theorem nonvanishingOpen_eq_top_iff {X : Scheme} (L : LineBundle X)
    (s : AlgebraicSection L.sheaf) :
    nonvanishingOpen L s = ⊤ ↔ IsIso s := by
  constructor
  · intro h
    apply (isIso_iff_stalk s).mpr
    intro x
    have hx : x ∈ nonvanishingOpen L s := by rw [h]; trivial
    obtain ⟨U, hU, hxU⟩ := TopologicalSpace.Opens.mem_sSup.mp hx
    exact (isIso_pullback_open_iff U s).mp hU ⟨x, hxU⟩
  · intro hs
    letI := hs
    apply top_unique
    apply le_sSup
    change IsIso ((Scheme.Modules.pullback (⊤ : X.Opens).ι).map s)
    infer_instance

theorem nonvanishingOpen_zero {X : Scheme} (L : LineBundle X) :
    nonvanishingOpen L 0 = ⊥ := by
  apply le_antisymm ?_ bot_le
  apply sSup_le
  intro U hU
  intro x hx
  have hres : IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      (0 : structureModule X ⟶ L.sheaf)) :=
    (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback U.ι)
      (0 : structureModule X ⟶ L.sheaf)).mpr hU
  let f := (Scheme.Modules.restrictFunctor U.ι).map (0 : structureModule X ⟶ L.sheaf)
  letI : IsIso f := hres
  have hid : (𝟙 ((structureModule X).restrict U.ι)) = 0 := by
    calc
      _ = f ≫ inv f := (IsIso.hom_inv_id f).symm
      _ = 0 := by
        change (Scheme.Modules.restrictFunctor U.ι).map
          (0 : structureModule X ⟶ L.sheaf) ≫ inv f = 0
        rw [Functor.map_zero, zero_comp]
  have hz := congrArg
    (fun q : (structureModule X).restrict U.ι ⟶ (structureModule X).restrict U.ι =>
      q.app ⊤ (1 : RingSections X (U.ι ''ᵁ ⊤))) hid
  change (1 : RingSections X (U.ι ''ᵁ ⊤)) = 0 at hz
  have hx' : x ∈ U.ι ''ᵁ ⊤ := by simpa only [Scheme.Opens.ι_image_top] using hx
  have hstalk := congrArg (X.presheaf.germ (U.ι ''ᵁ ⊤) x hx') hz
  exact (one_ne_zero (by simpa only [map_one, map_zero] using hstalk)).elim

end NonvanishingLocusProof
end


theorem nonvanishingOpen_zero {X : Scheme} (L : LineBundle X) :
    nonvanishingOpen L 0 = ⊥ := by
  exact NonvanishingLocusProof.nonvanishingOpen_zero L

theorem nonvanishingOpen_isIso {X : Scheme} (L : LineBundle X)
    (s : AlgebraicSection L.sheaf) :
    IsIso (restrictSection (nonvanishingOpen L s).ι s) := by
  exact NonvanishingLocusProof.nonvanishingOpen_isIso L s

theorem nonvanishingOpen_eq_top_iff {X : Scheme} (L : LineBundle X)
    (s : AlgebraicSection L.sheaf) :
    nonvanishingOpen L s = ⊤ ↔ IsIso s := by
  exact NonvanishingLocusProof.nonvanishingOpen_eq_top_iff L s

/- Source-only Phase 3 integration: ample_iso. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix

namespace AmpleIsoProofCandidate

set_option backward.isDefEq.respectTransparency false in
theorem restrictSection_postcompose_isIso_iff {X Y : Scheme} (f : Y ⟶ X)
    {E F : OModule X} (e : E ≅ F) (s : AlgebraicSection E) :
    IsIso (PhaseThree.restrictSection f (s ≫ e.hom)) ↔
      IsIso (PhaseThree.restrictSection f s) := by
  change IsIso ((Scheme.Modules.pullback f).map (s ≫ e.hom)) ↔
    IsIso ((Scheme.Modules.pullback f).map s)
  rw [CategoryTheory.Functor.map_comp]
  exact CategoryTheory.isIso_comp_right_iff
    ((Scheme.Modules.pullback f).map s) ((Scheme.Modules.pullback f).map e.hom)

theorem nonvanishingOpen_postcompose {X : Scheme} (L M : LineBundle X)
    (e : L.sheaf ≅ M.sheaf) (s : AlgebraicSection L.sheaf) :
    nonvanishingOpen M (s ≫ e.hom) = nonvanishingOpen L s := by
  unfold nonvanishingOpen
  apply congrArg sSup
  ext U
  exact restrictSection_postcompose_isIso_iff U.ι e s

def linePowerIso {X : Scheme} (L M : LineBundle X)
    (e : L.sheaf ≅ M.sheaf) (m : ℕ) :
    (linePower L m).sheaf ≅ (linePower M m).sheaf := by
  simpa only [linePower_sheaf_eq_tensorPower] using
    (SheafTensor.tensorPowerCongrIso e m)

theorem ample_of_iso {X : Scheme} (L M : LineBundle X)
    (e : L.sheaf ≅ M.sheaf) (hL : IsAmpleLine L) : IsAmpleLine M := by
  refine ⟨hL.1, ?_⟩
  intro x
  obtain ⟨m, hm, s, hx, ha⟩ := hL.2 x
  let p : (linePower L m).sheaf ≅ (linePower M m).sheaf := linePowerIso L M e m
  have hopen := nonvanishingOpen_postcompose (linePower L m) (linePower M m) p s
  refine ⟨m, hm, s ≫ p.hom, ?_, ?_⟩
  · simpa only [hopen] using hx
  · simpa only [hopen] using ha

theorem ample_iso {X : Scheme} (L M : LineBundle X)
    (e : L.sheaf ≅ M.sheaf) :
    IsAmpleLine L ↔ IsAmpleLine M := by
  exact ⟨ample_of_iso L M e, ample_of_iso M L e.symm⟩

end AmpleIsoProofCandidate
end


theorem ample_iso {X : Scheme} (L M : LineBundle X)
    (e : L.sheaf ≅ M.sheaf) :
    IsAmpleLine L ↔ IsAmpleLine M := by
  exact LeBrunSalamon.PhaseTwentySix.AmpleIsoProofCandidate.ample_iso (L := L) (M := M) (e := e)

/- Source-only Phase 3 integration: ample_positive_partial. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix

namespace AmplePositivePowerProofCandidate

def sectionPower {X : Scheme} (L : LineBundle X) (s : AlgebraicSection L.sheaf) :
    (r : ℕ) → AlgebraicSection (linePower L r).sheaf
  | 0 => 𝟙 (structureModule X)
  | r + 1 => (TensorConstruction.leftUnitIso (structureModule X)).inv ≫
      tensorMap (sectionPower L s r) s

set_option backward.isDefEq.respectTransparency false in
theorem restrictSection_postcompose_isIso_iff {X Y : Scheme} (f : Y ⟶ X)
    {E F : OModule X} (e : E ≅ F) (s : AlgebraicSection E) :
    IsIso (PhaseThree.restrictSection f (s ≫ e.hom)) ↔
      IsIso (PhaseThree.restrictSection f s) := by
  change IsIso ((Scheme.Modules.pullback f).map (s ≫ e.hom)) ↔
    IsIso ((Scheme.Modules.pullback f).map s)
  rw [CategoryTheory.Functor.map_comp]
  exact CategoryTheory.isIso_comp_right_iff
    ((Scheme.Modules.pullback f).map s) ((Scheme.Modules.pullback f).map e.hom)

theorem nonvanishingOpen_postcompose {X : Scheme} (L M : LineBundle X)
    (e : L.sheaf ≅ M.sheaf) (s : AlgebraicSection L.sheaf) :
    nonvanishingOpen M (s ≫ e.hom) = nonvanishingOpen L s := by
  unfold nonvanishingOpen
  apply congrArg sSup
  ext U
  exact restrictSection_postcompose_isIso_iff U.ι e s

theorem ample_of_positivePower {X : Scheme} (L : LineBundle X)
    (m : ℕ) (hm : 0 < m) (h : IsAmpleLine (linePower L m)) :
    IsAmpleLine L := by
  refine ⟨h.1, ?_⟩
  intro x
  obtain ⟨k, hk, s, hx, ha⟩ := h.2 x
  obtain ⟨e⟩ := linePower_mul L m k
  have hopen := nonvanishingOpen_postcompose
    (linePower (linePower L m) k) (linePower L (m * k)) e s
  refine ⟨m * k, Nat.mul_pos hm hk, s ≫ e.hom, ?_, ?_⟩
  · simpa only [hopen] using hx
  · simpa only [hopen] using ha

end AmplePositivePowerProofCandidate
end


end LeBrunSalamon.PhaseTwentySix

/- Positive tensor powers are ample exactly when the original invertible
sheaf is ample (Stacks Project 01PR and 01PT). The actual project line-power
construction is transported to recursive tensor powers in the proved wrapper. -/
section AmplePowerProofSection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix

namespace LeBrunSalamon.SheafAmpleness

/-- Nonvanishing of a line section means it locally trivializes the sheaf. -/
def nonvanishing {X : Scheme} (E : OModule X) (s : AlgebraicSection E) : X.Opens :=
  sSup {U : X.Opens | IsIso (restrictSection U.ι s)}

/-- Stacks 28.27.1 expressed on the actual sheaf and tensor-power construction. -/
def IsAmple {X : Scheme} (E : OModule X) : Prop :=
  CompactSpace X ∧ ∀ x : X,
    ∃ (m : ℕ) (_ : 0 < m) (s : AlgebraicSection (SheafTensor.tensorPower E m)),
      x ∈ nonvanishing (SheafTensor.tensorPower E m) s ∧
      IsAffineOpen (nonvanishing (SheafTensor.tensorPower E m) s)

theorem line_iff {X : Scheme} (L : LineBundle X) :
    IsAmpleLine L ↔ IsAmple L.sheaf := by
  unfold IsAmpleLine IsAmple
  apply and_congr_right
  intro _
  apply forall_congr'
  intro x
  apply exists_congr
  intro m
  apply exists_congr
  intro _
  let Q (E : OModule X) : Prop :=
    ∃ s : AlgebraicSection E,
      x ∈ nonvanishing E s ∧ IsAffineOpen (nonvanishing E s)
  change Q (linePower L m).sheaf ↔ Q (SheafTensor.tensorPower L.sheaf m)
  exact iff_of_eq (congrArg Q (linePower_sheaf_eq_tensorPower L m))

end LeBrunSalamon.SheafAmpleness

namespace LeBrunSalamon.PublishedInputs.Ample

/-- Stacks Project Lemma 28.27.2 (Tag 01PT), for an arbitrary invertible
module sheaf and a positive tensor power, with the quasi-compact convention
of Definition 28.27.1 (Tag 01PR). -/
theorem positive_tensorPower {X : Scheme} (E : OModule X)
    (hE : IsLocallyFreeOfRank E 1) (m : ℕ) (hm : 0 < m) :
    SheafAmpleness.IsAmple (SheafTensor.tensorPower E m) ↔
      SheafAmpleness.IsAmple E := by
  sorry

end LeBrunSalamon.PublishedInputs.Ample

namespace LeBrunSalamon.AmplePowerProof

theorem ample_positivePower_iff {X : Scheme} (L : LineBundle X)
    (m : ℕ) (hm : 0 < m) :
    IsAmpleLine (linePower L m) ↔ IsAmpleLine L := by
  rw [SheafAmpleness.line_iff, SheafAmpleness.line_iff,
    linePower_sheaf_eq_tensorPower]
  exact PublishedInputs.Ample.positive_tensorPower L.sheaf L.locallyFree m hm

end LeBrunSalamon.AmplePowerProof

end AmplePowerProofSection

namespace LeBrunSalamon.PhaseTwentySix
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive

theorem _root_.LeBrunSalamon.PublishedInputs.Step3e.ample_positivePower_iff
    {X : Scheme} (L : LineBundle X) (m : ℕ) (hm : 0 < m) :
    IsAmpleLine (linePower L m) ↔ IsAmpleLine L := by
  exact LeBrunSalamon.AmplePowerProof.ample_positivePower_iff L m hm

/-- Project-facing form of invariance of ampleness under positive tensor
powers. -/
theorem ample_positivePower_iff {X : Scheme} (L : LineBundle X)
    (m : ℕ) (hm : 0 < m) :
    IsAmpleLine (linePower L m) ↔ IsAmpleLine L := by
  exact LeBrunSalamon.PublishedInputs.Step3e.ample_positivePower_iff L m hm

theorem _root_.LeBrunSalamon.PublishedInputs.Step3e.determinant_shortExact
    {X : Scheme} {a b : ℕ}
    (E : AlgebraicVectorBundle X a)
    (F : AlgebraicVectorBundle X (a + b))
    (G : AlgebraicVectorBundle X b)
    (i : E.sheaf ⟶ F.sheaf) (p : F.sheaf ⟶ G.sheaf)
    (hz : i ≫ p = 0)
    (hex : (ShortComplex.mk i p hz).ShortExact) :
    Nonempty ((determinantLine F).sheaf ≅
      (tensorLine (determinantLine E) (determinantLine G)).sheaf) := by
  exact LeBrunSalamon.TangentDeterminantProof.determinant_shortExact E F G i p hz hex

/-- Project-facing determinant isomorphism for a short exact sequence of
finite locally free sheaves. -/
theorem determinant_shortExact {X : Scheme} {a b : ℕ}
    (E : AlgebraicVectorBundle X a)
    (F : AlgebraicVectorBundle X (a + b))
    (G : AlgebraicVectorBundle X b)
    (i : E.sheaf ⟶ F.sheaf) (p : F.sheaf ⟶ G.sheaf)
    (hz : i ≫ p = 0)
    (hex : (ShortComplex.mk i p hz).ShortExact) :
    Nonempty ((determinantLine F).sheaf ≅
      (tensorLine (determinantLine E) (determinantLine G)).sheaf) := by
  exact LeBrunSalamon.PublishedInputs.Step3e.determinant_shortExact
    E F G i p hz hex

end LeBrunSalamon.PhaseTwentySix

end
