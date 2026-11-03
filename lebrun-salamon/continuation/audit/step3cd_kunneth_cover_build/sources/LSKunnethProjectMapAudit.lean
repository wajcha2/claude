import LSKunnethDegreeZero
import RecompileExtensionsPart01

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Core.ExternalTensorCoordinates

/-- Exact equality of the original project map and the generic published
Künneth map, including their actual complex scalar structures. -/
theorem LeBrunSalamon.KunnethDegreeZero.originalMap_eq
    {Y : Scheme} (s : Y ⟶ ComplexBase) (E F : OModule Y) :
    globalTensorMap s E F = LeBrunSalamon.KunnethDegreeZero.canonicalMap s s E F := by
  rfl

theorem LeBrunSalamon.KunnethDegreeZero.originalMap_injective
    {d : ℕ} (X : SmoothProperComplexVariety d) (L M : LineBundle X.scheme) :
    Function.Injective (globalTensorMap X.structureMap L.sheaf M.sheaf) := by
  rw [LeBrunSalamon.KunnethDegreeZero.originalMap_eq]
  exact (LeBrunSalamon.KunnethDegreeZero.lineMap_bijective X L M).injective

#print axioms LeBrunSalamon.KunnethDegreeZero.exists_fin_tmul
#print axioms LeBrunSalamon.KunnethDegreeZero.originalMap_eq
#print axioms LeBrunSalamon.KunnethDegreeZero.originalMap_injective
#print axioms LeBrunSalamon.KunnethDegreeZero.externalSection_finiteSum

end
