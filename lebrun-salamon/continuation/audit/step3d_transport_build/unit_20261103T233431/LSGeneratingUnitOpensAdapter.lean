import LSGeneratingUnitOpens
import RecompileExtensionsPart04Geometry

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Skeleton

namespace LeBrunSalamon.GeneratingUnitOpensAdapter

theorem generating_sections_unitOpen {Y : Scheme} {N : ℕ}
    (L : LineBundle Y) (a : Fin (N+1) → AlgebraicSection L.sheaf)
    (ha : TupleGenerates L a) :
    ∃ U : Fin (N+1) → Y.Opens, iSup U = ⊤ ∧
      ∀ (i : Fin (N+1)) (T : Scheme) (f : T ⟶ Y),
        Set.range f ⊆ (U i : Set Y) ↔ IsIso (pullSection f (a i)) :=
  GeneratingUnitOpens.generating_sections_unitOpen L a ha

end LeBrunSalamon.GeneratingUnitOpensAdapter

end
