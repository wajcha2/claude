import LSEffectiveCartierInputs

/-! Transport the actual defining ideal and positive divisor line along
an isomorphism of closed subschemes over their common ambient scheme.
All comparisons are built from the actual structure-map kernels. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight

namespace LeBrunSalamon.EffectiveCartier

def idealIso_of_overIso {X X' Y : Scheme.{0}}
    (i : X ⟶ Y) (j : X' ⟶ Y) (e : X ≅ X') (he : e.hom ≫ j = i) :
    ideal i ≅ ideal j :=
  (P1Ideal.structureKernelIsoOfEq he).symm ≪≫
    P1Restriction.structureKernel_precomposeIso e j

def lineIso_of_idealIso {X X' Y : Scheme.{0}}
    (i : X ⟶ Y) (j : X' ⟶ Y)
    (hi : IsLocallyFreeOfRank (ideal i) 1) (hj : IsLocallyFreeOfRank (ideal j) 1)
    (e : ideal i ≅ ideal j) : (line i hi).sheaf ≅ (line j hj).sheaf :=
  internalHomGenericIso (ideal i) (structureModule Y) ≪≫
    HomConstruction.Generic.mapIso e (Iso.refl (structureModule Y)) ≪≫
    (internalHomGenericIso (ideal j) (structureModule Y)).symm

theorem cartier_of_overIso {X X' Y : Scheme.{0}}
    (i : X ⟶ Y) (j : X' ⟶ Y) (e : X ≅ X') (he : e.hom ≫ j = i)
    (hj : IsLocallyFreeOfRank (ideal j) 1) :
    ∃ hi : IsLocallyFreeOfRank (ideal i) 1,
      Nonempty ((line i hi).sheaf ≅ (line j hj).sheaf) := by
  let k := idealIso_of_overIso i j e he
  have hi : IsLocallyFreeOfRank (ideal i) 1 := locallyFreeOfRank_iso k.symm hj
  exact ⟨hi, ⟨lineIso_of_idealIso i j hi hj k⟩⟩

end LeBrunSalamon.EffectiveCartier
end
