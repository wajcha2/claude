import RecompileSections
import LSCohomologyHypotheses

/-!
The actual stalk of a line bundle is free of rank one, proved using the
specified local frame and germs. Composing this flat module with the actual
flat scheme stalk map proves relative flatness. This file introduces no
geometric input or admission. Off-graph native candidate.
-/

noncomputable section
set_option autoImplicit false
set_option maxErrors 1
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.LocalFrames

namespace LeBrunSalamon.LineStalkFlat

/-- Multiplication by the germ of the actual frame generator. -/
def frameMap {X : Scheme} {E : OModule X} {U : X.Opens}
    (e : OverFrame E U) {x : X} (hx : x ∈ U) :
    X.presheaf.stalk x →ₗ[X.presheaf.stalk x] E.presheaf.stalk x where
  toFun r := r • E.presheaf.germ U x hx (generator e)
  map_add' := fun r s => add_smul r s _
  map_smul' := fun r s => mul_smul r s _

theorem frameMap_germ {X : Scheme} {E : OModule X} {U V : X.Opens}
    (e : OverFrame E U) {x : X} (hx : x ∈ U)
    (i : V ⟶ U) (hxV : x ∈ V) (a : RingSections X V) :
    frameMap e hx (X.presheaf.germ V x hxV a) =
      E.presheaf.germ V x hxV (a • generator (restrict i e)) := by
  change X.presheaf.germ V x hxV a • E.presheaf.germ U x hx (generator e) = _
  calc
    X.presheaf.germ V x hxV a • E.presheaf.germ U x hx (generator e) =
        X.presheaf.germ V x hxV a •
          E.presheaf.germ V x hxV (generator (restrict i e)) := by
      congr 1
      rw [← generator_restrict i e]
      exact (E.presheaf.germ_res_apply i x hxV (generator e)).symm
    _ = _ := (PresheafOfModules.germ_smul E.val x V hxV a
      (generator (restrict i e))).symm

theorem frameMap_surjective {X : Scheme} {E : OModule X} {U : X.Opens}
    (e : OverFrame E U) {x : X} (hx : x ∈ U) :
    Function.Surjective (frameMap e hx) := by
  intro m
  obtain ⟨V, hVU, hxV, a, ha⟩ := E.presheaf.exists_le_germ_eq m hx
  refine ⟨X.presheaf.germ V x hxV (coordinates (restrict (homOfLE hVU) e) a), ?_⟩
  rw [frameMap_germ e hx (homOfLE hVU) hxV, reconstruct]
  exact ha

theorem frameMap_eq_zero {X : Scheme} {E : OModule X} {U : X.Opens}
    (e : OverFrame E U) {x : X} (hx : x ∈ U)
    (r : X.presheaf.stalk x) (h : frameMap e hx r = 0) : r = 0 := by
  obtain ⟨V, hVU, hxV, a, ha⟩ := X.presheaf.exists_le_germ_eq r hx
  let eV := restrict (homOfLE hVU) e
  have hz : E.presheaf.germ V x hxV (a • generator eV) =
      E.presheaf.germ V x hxV 0 := by
    rw [map_zero, ← frameMap_germ e hx (homOfLE hVU) hxV, ha]
    exact h
  obtain ⟨W, hxW, i, j, hW⟩ := E.presheaf.germ_eq x hxV hxV
    (a • generator eV) 0 hz
  rw [map_zero, Scheme.Modules.map_smul, generator_restrict] at hW
  have hc := congrArg (coordinates (restrict i eV)) hW
  simp only [map_smul, coordinates_generator, map_zero, smul_eq_mul, mul_one] at hc
  calc
    r = X.presheaf.germ V x hxV a := ha.symm
    _ = X.presheaf.germ W x hxW (X.presheaf.map i.op a) :=
      (X.presheaf.germ_res_apply i x hxW a).symm
    _ = 0 := by rw [hc, map_zero]

theorem frameMap_injective {X : Scheme} {E : OModule X} {U : X.Opens}
    (e : OverFrame E U) {x : X} (hx : x ∈ U) :
    Function.Injective (frameMap e hx) := by
  intro r s h
  apply sub_eq_zero.mp
  apply frameMap_eq_zero e hx
  rw [map_sub, h, sub_self]

/-- The linear equivalence uses the actual germ generator map. -/
def frameEquiv {X : Scheme} {E : OModule X} {U : X.Opens}
    (e : OverFrame E U) {x : X} (hx : x ∈ U) :
    X.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] E.presheaf.stalk x :=
  LinearEquiv.ofBijective (frameMap e hx)
    ⟨frameMap_injective e hx, frameMap_surjective e hx⟩

/-- The original rank-one generator data gives an actual local frame. -/
theorem exists_frame {X : Scheme} (L : LineBundle X) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ Nonempty (OverFrame L.sheaf U) := by
  obtain ⟨q, hq, hr⟩ := L.locallyFree
  letI := hq
  obtain ⟨i, hi⟩ := ((_root_.Opens.coversTop_iff X q.X).mp q.coversTop).exists_mem x
  let e : structureModule (q.X i).toScheme ≅ pullbackModule (q.X i).ι L.sheaf :=
    (coproductUniqueIso (fun _ : Fin 1 => structureModule (q.X i).toScheme)).symm ≪≫
      DominantSectionInjectivityProof.localFreePullbackIso q hr i
  exact ⟨q.X i, hi, ⟨ofOpenFrame (q.X i)
    (e ≪≫ ((Scheme.Modules.restrictFunctorIsoPullback (q.X i).ι).app L.sheaf).symm)⟩⟩

theorem line_stalk_flat {X : Scheme} (L : LineBundle X) (x : X) :
    Module.Flat (X.presheaf.stalk x) (L.sheaf.presheaf.stalk x) := by
  obtain ⟨U, hx, ⟨e⟩⟩ := exists_frame L x
  exact Module.Flat.of_linearEquiv (frameEquiv e hx).symm

/-- Relative flatness follows through the original stalk morphism, using
the module scalar action in `RelativelyFlat` itself. -/
theorem relativelyFlat {X S : Scheme} (p : X ⟶ S) [Flat p] (L : LineBundle X) :
    CohomologyHypotheses.RelativelyFlat p L.sheaf := by
  intro x
  letI : Algebra (S.presheaf.stalk (p x)) (X.presheaf.stalk x) :=
    (p.stalkMap x).hom.toAlgebra
  letI : Module (S.presheaf.stalk (p x)) (L.sheaf.presheaf.stalk x) :=
    Module.compHom (L.sheaf.presheaf.stalk x) (p.stalkMap x).hom
  letI : IsScalarTower (S.presheaf.stalk (p x)) (X.presheaf.stalk x)
      (L.sheaf.presheaf.stalk x) :=
    ⟨fun a b m => by
      change (((p.stalkMap x).hom a) * b) • m =
        ((p.stalkMap x).hom a) • (b • m)
      exact mul_smul _ _ _⟩
  haveI : Module.Flat (S.presheaf.stalk (p x)) (X.presheaf.stalk x) :=
    Flat.stalkMap p x
  haveI := line_stalk_flat L x
  exact Module.Flat.trans (S.presheaf.stalk (p x)) (X.presheaf.stalk x)
    (L.sheaf.presheaf.stalk x)

end LeBrunSalamon.LineStalkFlat

end
