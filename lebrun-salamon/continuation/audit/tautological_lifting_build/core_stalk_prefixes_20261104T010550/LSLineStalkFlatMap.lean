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

end LeBrunSalamon.LineStalkFlat
end
