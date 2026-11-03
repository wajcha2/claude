import LSBranchRamification

/-!
# Construction of the contact-value descent inputs

The finite image, normalization, all-sheet splitting and transverse
ramification arguments supply the geometric fields separately. Purity
and finite etale rigidity remain the exact reviewed classical inputs.
No final classification or first-jet target is used.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Core LeBrunSalamon.Skeleton

namespace LeBrunSalamon.Construction.Descent

/-- The original descent interface, filled by the individual constructions. -/
theorem constructedInputs : Inputs :=
  { lines := fun _ X hp => Lines.coveringFamily_exists X hp
    finiteImage := fun _ _ D => finiteValueImage_exists D
    normalize := by
      intro n X D I
      obtain ⟨N⟩ := normalizedImage_exists I
      exact ⟨N, goodOpen_exists N⟩
    splitSheets := fun _ _ D I N U H => allSheets_split D I N U H
    detectBranch := fun _ X hp _ _ N U H h => ramifiedTest_exists X hp N U H h
    purity := fun _ _ N h => purity_over_contactSquare N h
    rigidity := fun _ X N h => finiteEtale_contactSquare_trivial X N h
    graph := fun _ _ D I N h => finiteImage_graph_recovers_section D I N h }

end LeBrunSalamon.Construction.Descent

end

#print axioms LeBrunSalamon.Construction.Descent.constructedInputs
