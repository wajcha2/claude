import LSMovingPairConstruction

/-!
# Original project targets from the constructed inputs

These are the original public theorem names and statements. Their source
order follows the actual geometric construction so neither the first-jet
target nor the Riemannian target can be used to construct its own inputs.
The exact reviewed published inputs are still admitted leaves; this file
does not claim an admission-free proof. Native compilation and dependency
evidence are recorded with the checkpoint.
-/

noncomputable section
set_option autoImplicit false

open Bundle
open scoped Bundle ContDiff ENNReal BigOperators
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirtyFive LeBrunSalamon.Skeleton
open LeBrunSalamon.PhaseTen (TangentEvaluationAt)

namespace LeBrunSalamon.PhaseTwentyEight

/-- The original first-jet target, from the constructed global kernel. -/
theorem contactFano_firstJetGeneration_target {n : ℕ}
    (X : ContactFanoManifold n) :
    SeparatesFirstJets X.variety X.contact.sequence.line := by
  exact LeBrunSalamon.Construction.project_firstJets
    LeBrunSalamon.Construction.constructedAlgebraicInputs X

end LeBrunSalamon.PhaseTwentyEight

namespace LeBrunSalamon.PhaseThirtyFive

/-- The original Hamiltonian target and its original proof argument. -/
theorem contactFano_HamiltonianSpanning_target {n : ℕ}
    (X : ContactFanoManifold n) (x : ComplexPoint X.variety)
    (v : TangentEvaluationAt n (intrinsicAsCandidate X.variety X.contact) x) :
    ∃ s : AlgebraicSection X.contact.sequence.line.sheaf,
      restrictSection x.map
        (intrinsicHamiltonianSectionField X.variety X.contact s) = v := by
  exact intrinsicFirstJets_imply_HamiltonianSpanning X.variety X.contact
    (LeBrunSalamon.PhaseTwentyEight.contactFano_firstJetGeneration_target X) x v

end LeBrunSalamon.PhaseThirtyFive

namespace LeBrunSalamon

section Riemannian

variable (n : ℕ) (M : Type*)
variable [EMetricSpace M] [ChartedSpace (Model n) M]
variable [IsManifold (model n) ∞ M]
variable [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
variable [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
  (fun x : M => TangentSpace (model n) x)]
variable [IsRiemannianManifold (model n) M]

/-- The original dimension-at-least-eight Riemannian statement, using
the actual constructed project inputs and their reviewed classical
twistor and metric recovery inputs. -/
theorem leBrunSalamon
    [Nonempty M] [CompactSpace M] [ConnectedSpace M]
    (hn : 2 ≤ n)
    (hQK : IsPositiveQuaternionicKahler n M) :
    IsLocallyRiemannianSymmetric n M := by
  exact Construction.leBrunSalamon_project n M
    Construction.constructedProjectInputs hn hQK

end Riemannian
end LeBrunSalamon

end

#check LeBrunSalamon.PhaseTwentyEight.contactFano_firstJetGeneration_target
#print axioms LeBrunSalamon.PhaseTwentyEight.contactFano_firstJetGeneration_target
#check LeBrunSalamon.PhaseThirtyFive.contactFano_HamiltonianSpanning_target
#print axioms LeBrunSalamon.PhaseThirtyFive.contactFano_HamiltonianSpanning_target
#check LeBrunSalamon.leBrunSalamon
#print axioms LeBrunSalamon.leBrunSalamon
