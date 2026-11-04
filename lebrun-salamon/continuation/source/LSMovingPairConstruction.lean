import LSFormalArcComparison
import LSFamilyBivectorDescent
import LSProjectAssembly

/-!
# The actual moving-pair and project constructions

The rational sections are the sections descended from the represented
full family. Their regularity is tested on the actual total-space arcs,
including both marked source points and the complete special fibre.
Normal extension then supplies the two global vector lifts on the same
proper integral square. The whole-member comparisons are those already
constructed from the proper surjective reduced comparison covers.

No geometric construction is supplied as an extra input to these
theorems. Published geometric inputs remain the individually reviewed
leaves of the project; compilation and native dependency inspection are
recorded separately from these source proof terms.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Skeleton LeBrunSalamon.Refinement

namespace LeBrunSalamon.Construction

open StableMaps FamilyBivectors

namespace MovingPairConstruction

variable {n : ℕ} {X : ContactFanoManifold n}
variable {g : VeryFreeContactConic Lines.P Lines.marking X}
variable {N : FullConicNeighborhood Lines.P Lines.marking X g}
variable {F : ProjectiveNodalFamily Lines.P Lines.marking
  X.variety X.contact.sequence.line 2}
variable (Q : FullHomComparison Lines.P Lines.marking X.variety
  N.homSpace N.neighborhood X.contact.sequence.line 2 F)

/-- The actual descended pair has both height-one regularity properties.
The arc test uses the same rational domain as the constructed pair. -/
theorem extension_exists : Nonempty (SmoothFamily.rationalPair Q).Extension := by
  obtain ⟨S⟩ := Smoothing.standardSource_exists
  apply (SmoothFamily.rationalPair Q).extension_exists
    F.square_integralScheme F.square_normal F.square_noetherianOnAffines
  · apply F.regularAt_heightOne_of_arcs (MovingPair.leftBundle F.squareEvaluation)
    intro gamma hgamma
    exact FormalArcComparison.left_regular Q S gamma hgamma
  · apply F.regularAt_heightOne_of_arcs (MovingPair.rightBundle F.squareEvaluation)
    intro gamma hgamma
    exact FormalArcComparison.right_regular Q S gamma hgamma

include Q in
/-- The original full Hom neighborhood supplies dominance of the
same total family square used for the extension. -/
theorem dominant : DenseRange F.squareEvaluation.base :=
  Q.squareEvaluation_dominant N.smooth N.marked g.curve N.center.symm g.veryFree

include Q in
/-- Both regular vectors, their common contact value, and every full
source-square comparison are now data of the original interface. -/
theorem coveredMovingPair : Nonempty (CoveredMovingPair Lines.P Lines.marking X g) := by
  obtain ⟨E⟩ := extension_exists Q
  exact ⟨SmoothFamily.coveredMovingPair Q E (dominant Q)⟩

end MovingPairConstruction

/-- Construct the compactified family and its actual moving pair. -/
theorem coveredMovingPair_exists {n : ℕ} (X : ContactFanoManifold n)
    (g : VeryFreeContactConic Lines.P Lines.marking X) :
    Nonempty (CoveredMovingPair Lines.P Lines.marking X g) := by
  obtain ⟨⟨N, F, Q⟩⟩ := StableMaps.conicFamily_exists Lines.P Lines.marking X g
  exact MovingPairConstruction.coveredMovingPair Q

/-- The original extension interface, with its construction field
filled by actual geometry and its recovery fields by the proved full
source-square identities. -/
theorem constructedKernelExtensionInputs : KernelExtensionInputs :=
  kernelExtensionInputs_of_construction
    (fun _ X _ g => coveredMovingPair_exists X g)

theorem constructedAlgebraicInputs : AlgebraicInputs :=
  algebraicInputs_of_extension constructedKernelExtensionInputs

universe uR

theorem constructedProjectInputs : ProjectInputs.{uR} :=
  projectInputs_of_extension constructedKernelExtensionInputs

end LeBrunSalamon.Construction

end
