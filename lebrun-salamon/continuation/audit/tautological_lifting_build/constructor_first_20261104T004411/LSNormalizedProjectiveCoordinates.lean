import LSNormalizedProjectiveConstructor
import LSStandardTautologicalP1

/-!
Candidate project-facing constructor, retaining the public record type but
selecting its line, sections and frames from the same normalized generic
tautological data.  After native checking, this constructor body can replace
the current public choice, and these accessors can be transferred verbatim.
This file introduces no admitted theorem and remains outside source/.
-/

noncomputable section
set_option autoImplicit false
set_option maxErrors 1
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Core LeBrunSalamon.Skeleton

namespace LeBrunSalamon.NormalizedProjectiveCoordinates

/-- Actual sheaf comparison for the selected normalized public constructor. -/
def markedOneIso (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) :
    (coordinates 1).hyperplane.sheaf ≅ (projectiveTwist P p 1).sheaf :=
  StandardTautologicalP1.markedOneIso P p

theorem hyperplane_degree_one (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) :
    projectiveLineDegree P p (coordinates 1).hyperplane = 1 :=
  StandardTautologicalP1.degree_one P p

end LeBrunSalamon.NormalizedProjectiveCoordinates

end
