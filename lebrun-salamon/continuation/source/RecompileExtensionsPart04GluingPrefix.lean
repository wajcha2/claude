import RecompileExtensionsPart04Geometry

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

def leftAtNode {F : StandardSource} (m : SourceMarks F) (E : OModule (CentralFiber F))
    (s : AlgebraicSection (pullbackModule (leftBranch m) E)) :
    AlgebraicSection (pullbackModule (node m) E) :=
  pullSection marking.map s ≫
    (compositionPullback marking.map (leftBranch m) (node m) rfl E).hom

def rightAtNode {F : StandardSource} (m : SourceMarks F) (E : OModule (CentralFiber F))
    (s : AlgebraicSection (pullbackModule (rightBranch m) E)) :
    AlgebraicSection (pullbackModule (node m) E) :=
  pullSection marking.map s ≫
    (compositionPullback marking.map (rightBranch m) (node m)
      (branches_meet m).symm E).hom

/-- Normalize a pulled section along a specified composite. The nested
module composition is defined once over abstract schemes and maps. -/
def nodeEval {Y A N : Scheme}
    (f : A ⟶ Y) (p : N ⟶ A) (z : N ⟶ Y) (hz : p ≫ f = z)
    (E : OModule Y) (s : AlgebraicSection (pullbackModule f E)) :
    AlgebraicSection (pullbackModule z E) :=
  pullSection p s ≫ (compositionPullback p f z hz E).hom

/-- Compare the original left-node map with the generic normalized operation. -/
theorem leftAtNode_explicit {F : StandardSource} (m : SourceMarks F)
    (E : OModule (CentralFiber F))
    (s : AlgebraicSection (pullbackModule (leftBranch m) E)) :
    leftAtNode m E s = nodeEval (leftBranch m) marking.map (node m) rfl E s := by
  rfl

/-- The right marking reaches the named node. The theorem records the exact
endpoint before the equality is used in module comparison maps. -/
theorem rightBranch_to_node {F : StandardSource} (m : SourceMarks F) :
    marking.map ≫ rightBranch m = node m :=
  (branches_meet m).symm

end BundleGluing
end Normalization
end LeBrunSalamon.Construction
end
