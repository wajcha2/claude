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
set_option maxHeartbeats 50000
set_option synthInstance.maxHeartbeats 10000
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
    X.presheaf.stalk x →ₗ[X.presheaf.stalk x] E.presheaf.stalk x :=
  LinearMap.toSpanSingleton (X.presheaf.stalk x) (E.presheaf.stalk x)
    (E.presheaf.germ U x hx (generator e))

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

end LeBrunSalamon.LineStalkFlat
end
