import RecompileBasePart05C

/-! Generic external-product naturality, kept opaque at concrete curve carriers. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseEight LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight

namespace LeBrunSalamon.Construction.FamilyBivectors.ExternalProductFunctoriality

@[reassoc] theorem product_map {Y : Scheme} (s : Y ⟶ ComplexBase)
    {E E' F F' : OModule Y}
    (a : AlgebraicSection E) (b : AlgebraicSection F)
    (u : E ⟶ E') (v : F ⟶ F') :
    externalProductSection s a b ≫ externalTensorMap s u v =
      externalProductSection s (a ≫ u) (b ≫ v) := by
  simp only [externalProductSection, externalTensorMap, tensorSection_map,
    ExternalExchangeCoherenceProof.pullSection_map]

end LeBrunSalamon.Construction.FamilyBivectors.ExternalProductFunctoriality

end
