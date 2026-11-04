import LSDescentAssembly
import LSSmoothingAssembly
import LSConicJets
import LSClassicalActions
import LSClassicalReduction

/-!
# Assembly from the actual extension construction

All interfaces below retain their original definitions. The only
geometric argument of this assembly is the construction of the actual
proper moving-pair scheme with its two regular vector lifts and its
full curve-square comparisons. No existence of that argument is assumed
as a new axiom or inferred from the final project targets.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.PhaseThirtyFive LeBrunSalamon.Core LeBrunSalamon.Skeleton

namespace LeBrunSalamon.Construction

/-- The curve-square identity is recovered on the whole square by
surjective pullback. Symmetry follows from the full Hom neighborhood. -/
theorem kernelExtensionInputs_of_construction
    (h : ∀ (n : ℕ) (X : ContactFanoManifold n), HasPrimitiveContactPicard X.contact →
      ∀ g : VeryFreeContactConic Lines.P Lines.marking X,
        Nonempty (Refinement.CoveredMovingPair Lines.P Lines.marking X g)) :
    KernelExtensionInputs :=
  { construction := h
    recoverIdentity := fun _ X D f Q B hB =>
      Refinement.coveredComparison_recovers_identity Lines.P X D f Q B hB
    recoverSymmetry := fun _ X g H B hB =>
      Refinement.fullFamilyIdentity_symmetric Lines.P Lines.marking X g H B hB }

/-- The actual zero, first and second diagonal symbols, in their original order. -/
theorem constructedDiagonalInputs : Refinement.DiagonalInputs Lines.P Lines.marking :=
  { value := fun _ X g D =>
      Refinement.fullFamily_diagonalValue Lines.P Lines.marking X g D
    firstSymbol := fun _ X g D h =>
      Refinement.fullFamily_firstSymbol Lines.P Lines.marking X g D h
    secondSymbol := fun _ X g D h =>
      Refinement.fullFamily_secondSymbol Lines.P Lines.marking X g D h }

/-- The coefficient vector, its actual Taylor realization and the
commuting first-jet contraction formula fill the jet interface. -/
theorem constructedJetInputs : Refinement.Jets.Inputs :=
  { nonzero := fun _ _ _ K E _ F => Refinement.Jets.coefficient_value_nonzero K E F
    taylor := fun _ _ _ K E _ F => Refinement.Jets.taylorRealization_exists K E F
    contractions := fun _ _ _ _ E _ F ell =>
      Refinement.Jets.contraction_firstJet E F ell }

/-- Evaluation of the actual globally lifted Hamiltonian fields. -/
theorem constructedHamiltonianEvaluation : HamiltonianEvaluation := by
  intro n X h x v
  exact intrinsicFirstJets_imply_HamiltonianSpanning X.variety X.contact h x v

/-- The original algebraic project interface, conditional only on the
supplied extension construction and its ordinary comparison consequences. -/
theorem algebraicInputs_of_extension (K : KernelExtensionInputs) : AlgebraicInputs :=
  { nonprimitive := ClassicalReduction.nonprimitiveBranch
    smoothing := Smoothing.constructedInputs
    extension := K
    descent := Descent.constructedInputs
    diagonal := constructedDiagonalInputs
    jets := constructedJetInputs
    Hamiltonians := constructedHamiltonianEvaluation
    integration := ClassicalActions.algebraicIntegration
    classification := ClassicalReduction.homogeneousClassification }

universe uR

/-- The algebraic construction and the exact classical twistor/metric
inputs assemble into the original, universe-polymorphic project interface. -/
theorem projectInputs_of_extension (K : KernelExtensionInputs) : ProjectInputs.{uR} :=
  { algebraic := algebraicInputs_of_extension K
    riemannian := ClassicalReduction.riemannianInputs }

end LeBrunSalamon.Construction

end

#print axioms LeBrunSalamon.Construction.algebraicInputs_of_extension
#print axioms LeBrunSalamon.Construction.projectInputs_of_extension
