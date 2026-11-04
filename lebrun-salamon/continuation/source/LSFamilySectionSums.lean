import LSFamilyDescentTransport

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyEight

namespace LeBrunSalamon.Construction.FamilyBivectors.SectionSums

theorem pull_map_post_sum {T Y : Scheme} (k : T ⟶ Y)
    {A B : OModule Y} {C : OModule T}
    (c : A ⟶ B) (d : pullbackModule k B ⟶ C)
    {N : ℕ} (z : Fin N → AlgebraicSection A) :
    pullSection k ((∑ i, z i) ≫ c) ≫ d =
      ∑ i, pullSection k (z i ≫ c) ≫ d := by
  simp only [Preadditive.sum_comp, SectionTransport.pull_sum]

theorem pull_post_sum {T Y : Scheme} (k : T ⟶ Y)
    {A : OModule Y} {C : OModule T}
    (d : pullbackModule k A ⟶ C)
    {N : ℕ} (z : Fin N → AlgebraicSection A) :
    pullSection k (∑ i, z i) ≫ d =
      ∑ i, pullSection k (z i) ≫ d := by
  simp only [Preadditive.sum_comp, SectionTransport.pull_sum]

end LeBrunSalamon.Construction.FamilyBivectors.SectionSums

end
