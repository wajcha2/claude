import LSQuadraticSectionEvaluation

/-!
An invertible matrix satisfying the literal polynomial substitution
identity induces an actual isomorphism of quadratic zero schemes over
Spec R.  The isomorphism also preserves the pulled-back standard O(1).
All maps are obtained from the scheme-theoretic zero-locus universal
property, so no reducedness assumption or new admission is needed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Refinement

namespace LeBrunSalamon.QuadraticLinearTransport

/-- Vanishing is invariant under the prescribed pullback-line comparison,
with the pullback composition normalization kept explicit. -/
theorem pull_comp_zero_iff {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    {E : OModule Z} {F : OModule Y} (a : AlgebraicSection E)
    (b : AlgebraicSection F) (e : pullbackModule g E ≅ F)
    (he : pullSection g a ≫ e.hom = b) :
    pullSection (f ≫ g) a = 0 ↔ pullSection f b = 0 := by
  let c : pullbackModule (f ≫ g) E ≅ pullbackModule f F :=
    ((Scheme.Modules.pullbackComp f g).app E).symm ≪≫
      (Scheme.Modules.pullback f).mapIso e
  have hc : pullSection (f ≫ g) a ≫ c.hom = pullSection f b := by
    have h := StandardProjectiveBaseChange.composite_coordinate f g a e
      (Iso.refl (pullbackModule f F))
    simpa only [Iso.trans_refl, Iso.refl_hom, Category.comp_id, he] using h
  constructor
  · intro h
    rw [← hc, h, zero_comp]
  · intro h
    apply (cancel_mono c.hom).mp
    rw [hc, h, zero_comp]

variable (R : Type) [CommRing R]
variable (q q' : PlaneQuadratic.Coefficients R)
variable (M : (Matrix (Fin 3) (Fin 3) R)ˣ)
variable (hq : PlaneQuadratic.transformed R q M = PlaneQuadratic.polynomial R q')

include hq in
theorem forward_zero :
    pullSection (PlaneQuadratic.inclusion R q' ≫ (ProjectiveLinearAction.iso R 2 M).hom)
      (PlaneQuadratic.sectionOf R q) = 0 := by
  apply (pull_comp_zero_iff (PlaneQuadratic.inclusion R q')
    (ProjectiveLinearAction.iso R 2 M).hom (PlaneQuadratic.sectionOf R q)
    (PlaneQuadratic.sectionOf R q') (QuadraticSectionEvaluation.actionSquareIso M)
    (QuadraticSectionEvaluation.section_transformed q q' M hq)).mpr
  exact PlaneQuadratic.zero_equation R q'

include hq in
theorem backward_zero :
    pullSection (PlaneQuadratic.inclusion R q ≫ (ProjectiveLinearAction.iso R 2 M).inv)
      (PlaneQuadratic.sectionOf R q') = 0 := by
  apply (pull_comp_zero_iff
    (PlaneQuadratic.inclusion R q ≫ (ProjectiveLinearAction.iso R 2 M).inv)
    (ProjectiveLinearAction.iso R 2 M).hom (PlaneQuadratic.sectionOf R q)
    (PlaneQuadratic.sectionOf R q') (QuadraticSectionEvaluation.actionSquareIso M)
    (QuadraticSectionEvaluation.section_transformed q q' M hq)).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact PlaneQuadratic.zero_equation R q

def forward : PlaneQuadratic.ZeroScheme R q' ⟶ PlaneQuadratic.ZeroScheme R q :=
  Classical.choose (PlaneQuadratic.universal R q
    (PlaneQuadratic.inclusion R q' ≫ (ProjectiveLinearAction.iso R 2 M).hom)
    (forward_zero R q q' M hq))

theorem forward_inclusion : forward R q q' M hq ≫ PlaneQuadratic.inclusion R q =
    PlaneQuadratic.inclusion R q' ≫ (ProjectiveLinearAction.iso R 2 M).hom :=
  (Classical.choose_spec (PlaneQuadratic.universal R q
    (PlaneQuadratic.inclusion R q' ≫ (ProjectiveLinearAction.iso R 2 M).hom)
    (forward_zero R q q' M hq))).1

def backward : PlaneQuadratic.ZeroScheme R q ⟶ PlaneQuadratic.ZeroScheme R q' :=
  Classical.choose (PlaneQuadratic.universal R q'
    (PlaneQuadratic.inclusion R q ≫ (ProjectiveLinearAction.iso R 2 M).inv)
    (backward_zero R q q' M hq))

theorem backward_inclusion : backward R q q' M hq ≫ PlaneQuadratic.inclusion R q' =
    PlaneQuadratic.inclusion R q ≫ (ProjectiveLinearAction.iso R 2 M).inv :=
  (Classical.choose_spec (PlaneQuadratic.universal R q'
    (PlaneQuadratic.inclusion R q ≫ (ProjectiveLinearAction.iso R 2 M).inv)
    (backward_zero R q q' M hq))).1

/-- Orientation: q(Mx)=q'(x) gives Zero(q') ≅ Zero(q). -/
def iso : PlaneQuadratic.ZeroScheme R q' ≅ PlaneQuadratic.ZeroScheme R q where
  hom := forward R q q' M hq
  inv := backward R q q' M hq
  hom_inv_id := by
    apply (cancel_mono (PlaneQuadratic.inclusion R q')).mp
    rw [Category.assoc, backward_inclusion, ← Category.assoc, forward_inclusion]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (PlaneQuadratic.inclusion R q)).mp
    rw [Category.assoc, forward_inclusion, ← Category.assoc, backward_inclusion]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]

theorem over_base : (iso R q q' M hq).hom ≫ PlaneQuadratic.projection R q =
    PlaneQuadratic.projection R q' := by
  change forward R q q' M hq ≫
    (PlaneQuadratic.inclusion R q ≫ StandardTautological.toSpec R 2) = _
  rw [← Category.assoc, forward_inclusion, Category.assoc, ProjectiveLinearAction.over_base]
  rfl

/-- The same zero-scheme isomorphism preserves the actual restricted standard
tautological line, through the specified matrix action comparison. -/
def lineIso :
    pullbackModule (iso R q q' M hq).hom
      (pullbackModule (PlaneQuadratic.inclusion R q) (StandardTautological.line R 2).sheaf) ≅
    pullbackModule (PlaneQuadratic.inclusion R q') (StandardTautological.line R 2).sheaf :=
  (Scheme.Modules.pullbackComp (iso R q q' M hq).hom
      (PlaneQuadratic.inclusion R q)).app (StandardTautological.line R 2).sheaf ≪≫
    (Scheme.Modules.pullbackCongr (forward_inclusion R q q' M hq)).app
      (StandardTautological.line R 2).sheaf ≪≫
    ((Scheme.Modules.pullbackComp (PlaneQuadratic.inclusion R q')
      (ProjectiveLinearAction.iso R 2 M).hom).app (StandardTautological.line R 2).sheaf).symm ≪≫
    (Scheme.Modules.pullback (PlaneQuadratic.inclusion R q')).mapIso
      (ProjectiveLinearAction.lineIso R 2 M)

end LeBrunSalamon.QuadraticLinearTransport
end
