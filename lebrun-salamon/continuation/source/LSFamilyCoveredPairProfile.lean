import LSFamilyDescentReparametrization
import LSOpenSectionTransport
import LSFamilySmoothCoordinates
import LSFamilySmoothPointValues
import LSFamilySmoothDescent

/-!
# Open-section comparison and smooth-family descent of the actual tensors.

This namespace block is extracted verbatim from the candidate descent
source. Public names, statements and proof bodies are retained. The preceding
transport blocks are imported so each completed native output can be reused.
-/

noncomputable section
set_option autoImplicit false
set_option profiler true
set_option stderrAsMessages false
set_option maxErrors 1
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyFive
open LeBrunSalamon.Core LeBrunSalamon.Skeleton LeBrunSalamon.Refinement
open LeBrunSalamon.PhaseTwentyEight.ExternalExchangeCoherenceProof

namespace LeBrunSalamon.Construction.FamilyBivectors


-- Normalize the existing P1/contact carrier aliases for the same actual maps.
set_option allowUnsafeReducibility true
attribute [local reducible] projectiveLineVariety identityCurveContact intrinsicTangentBundle

namespace SmoothFamily

variable {P : ProjectiveLineOverC} {p : ProjectiveLinePoint P}
variable {n : ℕ} {X : ContactFanoManifold n} {g : VeryFreeContactConic P p X}
variable {N : FullConicNeighborhood P p X g}
variable {F : StableMaps.ProjectiveNodalFamily P p X.variety X.contact.sequence.line 2}
variable (Q : StableMaps.FullHomComparison P p X.variety N.homSpace N.neighborhood
  X.contact.sequence.line 2 F)


variable (t : PointsOver ComplexBase (𝟙 ComplexBase) N.neighborhood.toScheme
  (N.neighborhood.ι ≫ N.homSpace.toC))

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "DESCENT_FINAL2_STAGE ENTER_coveredComparison"
  err.flush

/-- An actual extension yields the exact original covered-curve
comparison. The contact value is the original normalized source tensor. -/
def coveredComparison (E : (rationalPair Q).Extension)
    (hp : IsProper F.squareEvaluation)
    (hd : DenseRange (fun y : F.Square => F.squareEvaluation y)) :
    CoveredCurveComparison P X (E.properPair hp hd F.square_integralScheme) (N.curveAt t) where
  cover := Q.ReducedMemberCover t
  toSquare := Q.reducedMemberToSquare t
  proper := Q.reducedMemberToSquare_proper t
  surjective := Q.reducedMemberToSquare_surjective t
  toSource := memberToFamily Q t
  commutes := memberToFamily_evaluation Q t
  identity := by
    rw [E.properPair_value hp hd F.square_integralScheme, pullSection_naturality]
    simp only [Category.assoc]
    rw [pullbackSquare_naturality, ← Category.assoc, extension_left_member Q t E,
      ← pullSection_naturality, Curve.leftSection_contact]

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "DESCENT_FINAL2_STAGE EXIT_coveredComparison"
  err.flush

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "DESCENT_FINAL2_STAGE ENTER_coveredMovingPair"
  err.flush

/-- The original covered moving-pair output follows from extension of
the two rational sections. All full-family comparisons are constructed,
rather than added as a field of an auxiliary hypothesis package. -/
def coveredMovingPair (E : (rationalPair Q).Extension)
    (hd : DenseRange (fun y : F.Square => F.squareEvaluation y)) :
    CoveredMovingPair P p X g where
  properPair := E.properPair F.squareEvaluation_proper hd F.square_integralScheme
  fullFamily := N
  comparison := fun t => coveredComparison Q t E F.squareEvaluation_proper hd

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "DESCENT_FINAL2_STAGE EXIT_coveredMovingPair"
  err.flush

end SmoothFamily

end LeBrunSalamon.Construction.FamilyBivectors

end
