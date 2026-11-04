import RecompileSections

/-!
# Coefficients of the actual tangent action in a normalized frame

The calculation is proved for an arbitrary scheme, open and tangent frame.
It then applies to the already constructed derivative frames on P¹.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.LocalFrames

namespace LeBrunSalamon.TangentFrameCoordinates

theorem action_coordinate {Y : Scheme} (s : Y ⟶ ComplexBase) (U : Y.Opens)
    (e : OverFrame (tangentSheaf s) U) (z : RingSections Y U)
    (he : tangentActs s U (generator e) z = 1)
    (v : SectionsOn (tangentSheaf s) U) :
    tangentActs s U v z = coordinates e v := by
  have h := congrArg (fun w : SectionsOn (tangentSheaf s) U =>
    tangentActs s U w z) (reconstruct e v)
  rw [TangentActionProof.smul_field, he, mul_one] at h
  exact h.symm

theorem action_bijective {Y : Scheme} (s : Y ⟶ ComplexBase) (U : Y.Opens)
    (e : OverFrame (tangentSheaf s) U) (z : RingSections Y U)
    (he : tangentActs s U (generator e) z = 1) :
    Function.Bijective (fun v : SectionsOn (tangentSheaf s) U => tangentActs s U v z) := by
  constructor
  · intro v w h
    apply (coordinates e).injective
    exact (action_coordinate s U e z he v).symm.trans
      (h.trans (action_coordinate s U e z he w))
  · intro a
    refine ⟨(coordinates e).symm a, ?_⟩
    exact (action_coordinate s U e z he ((coordinates e).symm a)).trans
      ((coordinates e).apply_symm_apply a)

end LeBrunSalamon.TangentFrameCoordinates

end
