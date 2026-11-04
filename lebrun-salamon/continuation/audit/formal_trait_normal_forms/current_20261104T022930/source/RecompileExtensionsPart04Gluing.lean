import RecompileExtensionsPart04GluingPrefix

noncomputable section

set_option autoImplicit false
open Bundle
open scoped Bundle ContDiff ENNReal
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 100] LieRing.ofAssociativeRing
open CategoryTheory
open AlgebraicGeometry
open CategoryTheory.Limits

namespace LeBrunSalamon.Construction

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseThree LeBrunSalamon.PhaseSeven
open LeBrunSalamon.PhaseEight LeBrunSalamon.PhaseTen
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.PhaseThirtyFour LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Core LeBrunSalamon.Skeleton

namespace Normalization
open Lines Smoothing

namespace BundleGluing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Compare the original right-node map with the generic normalized operation. -/
theorem rightAtNode_explicit {F : StandardSource} (m : SourceMarks F)
    (E : OModule (CentralFiber F))
    (s : AlgebraicSection (pullbackModule (rightBranch m) E)) :
    rightAtNode m E s =
      nodeEval (rightBranch m) marking.map (node m) (rightBranch_to_node m) E s := by
  exact congrArg
    (fun h : marking.map ≫ rightBranch m = node m =>
      nodeEval (rightBranch m) marking.map (node m) h E s)
    (Subsingleton.elim (branches_meet m).symm (rightBranch_to_node m))


end BundleGluing
end Normalization
end LeBrunSalamon.Construction
end
