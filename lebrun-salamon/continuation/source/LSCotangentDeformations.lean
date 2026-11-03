import LSHomVelocity

/-!
# The normalized first-order cotangent comparison

The inverse is constructed on functions by `a ↦ f#(a) + ε D(a)`.
The existing dual-thickening normal-form theorem is used explicitly; no
additional deformation-theoretic existence assertion is assumed here.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Lines.FamilyVariation

open DualThickening

private theorem presheafed_ext_app {Y X : Scheme}
    {p q : Y.toPresheafedSpace ⟶ X.toPresheafedSpace}
    (hb : p.base = q.base)
    (ha : ∀ V, p.c.app (op V) ≫ Y.presheaf.map
      (eqToHom congr((TopologicalSpace.Opens.map $hb.symm).obj V)).op =
        q.c.app (op V)) : p = q := by
  apply PresheafedSpace.ext p q hb
  exact TopCat.Presheaf.ext (fun V => by simpa using! ha V)

/-- Localness can be checked after a surjective morphism on the source
when the composite is already a morphism of locally ringed spaces. -/
private theorem local_of_surjective_composite {Y T X : Scheme}
    (i : Y ⟶ T) (hi : Function.Surjective i)
    (q : T.toPresheafedSpace ⟶ X.toPresheafedSpace)
    (f : Y ⟶ X) (hf : i.toPshHom ≫ q = f.toPshHom)
    (x : T) : IsLocalHom (q.stalkMap x).hom := by
  obtain ⟨y, rfl⟩ := hi x
  have hlocal : ∀ y, IsLocalHom ((i.toPshHom ≫ q).stalkMap y).hom := by
    rw [hf]
    intro y
    exact f.prop y
  haveI : IsLocalHom (((i.stalkMap y).hom).comp
      ((q.stalkMap (i y)).hom)) := by
    have h := hlocal y
    rw [PresheafedSpace.stalkMap.comp] at h
    exact h
  exact isLocalHom_of_comp (q.stalkMap (i y)).hom (i.stalkMap y).hom

theorem Deformation.onFunction_ext {Y X : Scheme}
    {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase} {f : Y ⟶ X}
    {D₁ D₂ : Deformation sY sX f}
    (h : ∀ (V : X.Opens) (a : RingSections X V),
      D₁.onFunction V a = D₂.onFunction V a) : D₁ = D₂ := by
  apply Deformation.ext
  have hb : D₁.map.base = D₂.map.base := by
    ext y
    exact (family_apply_eq_centre sY D₁.map f D₁.reduces y).trans
      (family_apply_eq_centre sY D₂.map f D₂.reduces y).symm
  apply Scheme.Hom.ext hb
  intro V
  have hp : functionPullback sY D₁.map f D₁.reduces V =
      functionPullback sY D₂.map f D₂.reduces V := by
    ext a
    apply coefficients_ext
    · rw [reductionCoefficient_functionPullback, reductionCoefficient_functionPullback]
    · exact h V a
  apply (cancel_mono ((space sY).presheaf.map
    (eqToHom (preimage_eq sY D₂.map f D₂.reduces V).symm).op)).mp
  dsimp only [functionPullback, Scheme.Hom.appLE] at hp
  simp only [Category.assoc, ← Functor.map_comp]
  convert hp using 1 <;> congr 2

/-- Equality of the normalized cotangent functionals determines the actual
first-order morphism, not just its map on reduced points. -/
theorem Deformation.cotangentHom_injective {Y X : Scheme}
    {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase} {f : Y ⟶ X} :
    Function.Injective (fun D : Deformation sY sX f => D.cotangentHom) := by
  intro D₁ D₂ h
  apply Deformation.onFunction_ext
  intro V a
  exact (D₁.cotangentHom_differential V a).symm.trans
    ((congrArg (fun q : pullbackModule f (cotangentSheaf sX) ⟶ structureModule Y =>
      q.app (f ⁻¹ᵁ V) (pullLocalSection f (cotangentSheaf sX) V
        ((cotangentPresentation sX).differential.apply V a))) h).trans
          (D₂.cotangentHom_differential V a))

namespace FromDerivation

variable {Y X : Scheme} {sY : Y ⟶ ComplexBase} {sX : X ⟶ ComplexBase}
  {f : Y ⟶ X}

abbrev Derivation :=
  RelativeSheafDerivation sX ((Scheme.Modules.pushforward f).obj (structureModule Y))

variable (D : Derivation (sX := sX) (f := f))

theorem apply_one (V : X.Opens) : D.apply V 1 = 0 := by
  have h := D.leibniz V 1 1
  simp only [one_mul, one_smul] at h
  exact (add_left_cancel (show D.apply V 1 + 0 = D.apply V 1 + D.apply V 1 by
    simpa only [add_zero] using h)).symm

/-- The ring map on every target open, with the prescribed epsilon. -/
def app (sY : Y ⟶ ComplexBase) (V : X.Opens) :
    X.presheaf.obj (op V) ⟶
      (space sY).presheaf.obj (op (projection sY ⁻¹ᵁ (f ⁻¹ᵁ V))) :=
  CommRingCat.ofHom
    { toFun := fun a => normalForm sY (f ⁻¹ᵁ V) (f.app V a) (D.apply V a)
      map_zero' := by rw [map_zero, D.zero, normalForm_zero]
      map_one' := by rw [map_one, apply_one]; simp [normalForm]
      map_add' := by
        intro a b
        rw [map_add, D.add, normalForm_add]
      map_mul' := by
        intro a b
        rw [map_mul, D.leibniz]
        exact (normalForm_mul sY (f ⁻¹ᵁ V)
          (f.app V a) (D.apply V a) (f.app V b) (D.apply V b)).symm }

theorem app_naturality (sY : Y ⟶ ComplexBase)
    {U V : X.Opens} (i : U ⟶ V) :
    X.presheaf.map i.op ≫ app D sY U = app D sY V ≫
      (space sY).presheaf.map
        (((TopologicalSpace.Opens.map (projection sY).base).map
          ((TopologicalSpace.Opens.map f.base).map i)).op) := by
  ext a
  change normalForm sY (f ⁻¹ᵁ U)
    (f.app U (X.presheaf.map i.op a)) (D.apply U (X.presheaf.map i.op a)) =
      (space sY).presheaf.map
        (((TopologicalSpace.Opens.map (projection sY).base).map
          ((TopologicalSpace.Opens.map f.base).map i)).op)
        (normalForm sY (f ⁻¹ᵁ V) (f.app V a) (D.apply V a))
  rw [normalForm_restrict]
  congr 1
  · exact congrArg (fun k => k a) (f.naturality i.op)
  · exact (D.naturality i a).symm

/-- The derivation determines a morphism of presheafed spaces on the
underlying continuous map of the constant family. -/
def presheafedMap (sY : Y ⟶ ComplexBase) :
    (space sY).toPresheafedSpace ⟶ X.toPresheafedSpace where
  base := (projection sY ≫ f).base
  c :=
    { app := fun V => app D sY V.unop
      naturality := fun _ _ i => app_naturality D sY i.unop }

theorem presheafedMap_reduces (sY : Y ⟶ ComplexBase) :
    (zeroSection sY).toPshHom ≫ presheafedMap D sY = f.toPshHom := by
  have hb : ((zeroSection sY).toPshHom ≫ presheafedMap D sY).base =
      f.toPshHom.base := by
    change (zeroSection sY ≫ projection sY ≫ f).base = f.base
    rw [← Category.assoc, zeroSection_projection, Category.id_comp]
  apply presheafed_ext_app hb
  intro V
  change app D sY V ≫ (zeroSection sY).app (projection sY ⁻¹ᵁ (f ⁻¹ᵁ V)) ≫
    Y.presheaf.map _ = f.app V
  change app D sY V ≫ reductionHom sY (f ⁻¹ᵁ V) = f.app V
  ext a
  exact reductionHom_normalForm sY (f ⁻¹ᵁ V) (f.app V a) (D.apply V a)

/-- The function formula is local on stalks because its reduction is
the given scheme morphism and the zero section is surjective on points. -/
def schemeMap (sY : Y ⟶ ComplexBase) : space sY ⟶ X where
  toLRSHom' :=
    { toHom := presheafedMap D sY
      prop := local_of_surjective_composite (zeroSection sY)
        (StandardInputs.InfinitesimalGeometry.dualThickening_zeroSection_surjective sY)
        (presheafedMap D sY) f (presheafedMap_reduces D sY) }

theorem schemeMap_reduces (sY : Y ⟶ ComplexBase) :
    zeroSection sY ≫ schemeMap D sY = f := by
  apply Scheme.Hom.ext'
  apply LocallyRingedSpace.Hom.ext'
  exact presheafedMap_reduces D sY

theorem schemeMap_overC (sY : Y ⟶ ComplexBase) (hf : f ≫ sX = sY) :
    schemeMap D sY ≫ sX = toC sY := by
  suffices h : schemeMap D sY ≫ sX = projection sY ≫ (f ≫ sX) by
    rw [hf] at h
    exact h
  have hb : (schemeMap D sY ≫ sX).base =
      (projection sY ≫ (f ≫ sX)).base := rfl
  apply Scheme.Hom.ext hb
  intro W
  simp only [eqToHom_refl, op_id, CategoryTheory.Functor.map_id,
    Category.comp_id]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  ext a
  change normalForm sY (f ⁻¹ᵁ (sX ⁻¹ᵁ W))
    (f.app (sX ⁻¹ᵁ W) (sX.app W a))
    (D.apply (sX ⁻¹ᵁ W) (sX.app W a)) =
      (projection sY).app (f ⁻¹ᵁ (sX ⁻¹ᵁ W))
        (f.app (sX ⁻¹ᵁ W) (sX.app W a))
  rw [D.killsBase]
  simp [normalForm]

def deformation (sY : Y ⟶ ComplexBase) (hf : f ≫ sX = sY) :
    Deformation sY sX f where
  map := schemeMap D sY
  overC := schemeMap_overC D sY hf
  reduces := schemeMap_reduces D sY

theorem deformation_onFunction (sY : Y ⟶ ComplexBase)
    (hf : f ≫ sX = sY) (V : X.Opens) (a : RingSections X V) :
    (deformation D sY hf).onFunction V a = D.apply V a := by
  unfold Deformation.onFunction functionPullback Scheme.Hom.appLE
  change coefficient sY (f ⁻¹ᵁ V)
    ((app D sY V ≫ (space sY).presheaf.map (𝟙 _)) a) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact coefficient_normalForm sY (f ⁻¹ᵁ V) (f.app V a) (D.apply V a)

theorem deformation_derivation (sY : Y ⟶ ComplexBase) (hf : f ≫ sX = sY) :
    (deformation D sY hf).derivation = D := by
  apply relativeDerivation_ext
  exact deformation_onFunction D sY hf

end FromDerivation

/-- Every functional on the actual relative cotangent sheaf is realized
by the explicit epsilon-normalized deformation. -/
theorem Deformation.cotangentHom_surjective {Y X : Scheme}
    (sY : Y ⟶ ComplexBase) (sX : X ⟶ ComplexBase)
    (f : Y ⟶ X) (hf : f ≫ sX = sY) :
    Function.Surjective (fun D : Deformation sY sX f => D.cotangentHom) := by
  intro h
  let h' := (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ h
  let D := (cotangentPresentation sX).differential.postcompose h'
  refine ⟨FromDerivation.deformation D sY hf, ?_⟩
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Deformation.cotangentHom_adjoint, FromDerivation.deformation_derivation]
  exact (differentialLift_unique D h' rfl).symm

/-- The first-order comparison uses its original, prescribed map on local
differentials; both injectivity and surjectivity are now proved. -/
theorem Deformation.cotangentHom_bijective {Y X : Scheme}
    (sY : Y ⟶ ComplexBase) (sX : X ⟶ ComplexBase)
    (f : Y ⟶ X) (hf : f ≫ sX = sY) :
    Function.Bijective (fun D : Deformation sY sX f => D.cotangentHom) :=
  ⟨Deformation.cotangentHom_injective,
    Deformation.cotangentHom_surjective sY sX f hf⟩

end LeBrunSalamon.Construction.Lines.FamilyVariation

end
