import LSFamilyDescentTransport

/-!
# Canonical conversion between open-scheme sections and section values

The six existing OpenSection declarations are preserved verbatim here.
Their dependency is the generic transport layer, so formal-arc regularity
can use them without importing the full smooth-family descent argument.
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
open LeBrunSalamon.PhaseTwentyEight.ExternalExchangeCoherenceProof

namespace LeBrunSalamon.Construction.FamilyBivectors


-- Normalize the existing P1/contact carrier aliases for the same actual maps.
set_option allowUnsafeReducibility true
attribute [local reducible] projectiveLineVariety identityCurveContact intrinsicTangentBundle

namespace OpenSection

/-- A section on the pulled-back module over an open subscheme gives
the actual section of the original sheaf on that open. -/
def value {Y : Scheme} (U : Y.Opens) {E : OModule Y}
    (s : AlgebraicSection (pullbackModule U.ι E)) : SectionsOn E U :=
  E.presheaf.map (eqToHom U.ι_image_top.symm).op
    (sectionValue (s ≫ (Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app E))

/-- The inverse construction retains the canonical open pullback. -/
def fromValue {Y : Scheme} (U : Y.Opens) {E : OModule Y}
    (s : SectionsOn E U) : AlgebraicSection (pullbackModule U.ι E) :=
  sectionFromValue (E.presheaf.map (eqToHom U.ι_image_top).op s) ≫
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app E

theorem value_section {Y : Scheme} (U : Y.Opens) {E : OModule Y}
    (s : SectionsOn E U) : value U (fromValue U s) = s := by
  simp only [value, fromValue, Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
    sectionFromValue_spec, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← op_comp, eqToHom_trans, eqToHom_refl, CategoryTheory.Functor.map_id]
  rfl

theorem section_value {Y : Scheme} (U : Y.Opens) {E : OModule Y}
    (s : AlgebraicSection (pullbackModule U.ι E)) : fromValue U (value U s) = s := by
  apply (cancel_mono ((Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app E)).mp
  simp only [fromValue, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  apply (sectionValue_bijective (E.restrict U.ι)).injective
  simp only [sectionFromValue_spec, value, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl, CategoryTheory.Functor.map_id]
  rfl

theorem value_map {Y : Scheme} (U : Y.Opens) {E F : OModule Y}
    (s : AlgebraicSection (pullbackModule U.ι E)) (v : E ⟶ F) :
    value U (s ≫ (Scheme.Modules.pullback U.ι).map v) = v.app U (value U s) := by
  unfold value
  rw [Category.assoc, (Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.naturality,
    ← Category.assoc, sectionValue_comp]
  exact sheafHom_naturality v (eqToHom U.ι_image_top.symm)
    (sectionValue (s ≫ (Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app E))

theorem value_pullSection {Y : Scheme} (U : Y.Opens) {E : OModule Y}
    (s : AlgebraicSection E) :
    value U (pullSection U.ι s) =
      E.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (sectionValue s) := by
  rw [← FrameEvaluation.restrictedSection_to_pullSection]
  simp only [value, Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
    FrameEvaluation.restrictedSection_value, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp, ← op_comp]
  rfl

end OpenSection

end LeBrunSalamon.Construction.FamilyBivectors

end
