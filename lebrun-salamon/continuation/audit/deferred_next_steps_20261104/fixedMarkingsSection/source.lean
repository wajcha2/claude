import RecompileExtensionsPart02
import LSContactCompletion

noncomputable section
set_option autoImplicit false
set_option profiler true
set_option stderrAsMessages false
set_option maxErrors 1

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.Skeleton LeBrunSalamon.Refinement
open LeBrunSalamon.Construction.Lines

/-! Ordinary scheme-map comparisons for fixed markings in the actual
two-point source. No smoothness of the projective line, Hom smoothness,
target irreducibility, infinitesimal comparison, or dominance theorem is used.
-/

namespace LeBrunSalamon.Next3i.FixedMarkings

variable (P : ProjectiveLineOverC) (p q : ProjectiveLinePoint P)
variable {d : ℕ} {X : SmoothProperComplexVariety d}
variable (H : HomSpacePresentation P X) (U : H.parameter.Opens)

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "FIXED_MARKINGS_STAGE ENTER_PAIR"
  err.flush

def pairMap : ComplexBase ⟶ SelfProduct P.structureMap :=
  pullback.lift p.map q.map (p.overC.trans q.overC.symm)

theorem pairMap_first :
    pairMap P p q ≫ firstProjection P.structureMap = p.map :=
  pullback.lift_fst _ _ _

theorem pairMap_second :
    pairMap P p q ≫ secondProjection P.structureMap = q.map :=
  pullback.lift_snd _ _ _

theorem pairMap_overC :
    pairMap P p q ≫ HomTwoPointEvaluation.squareStructure P = 𝟙 ComplexBase := by
  rw [HomTwoPointEvaluation.squareStructure, ← Category.assoc,
    pairMap_first, p.overC]

/-- Two marked evaluations on the original representing parameter. -/
def pairedEvaluation : H.parameter ⟶ SelfProduct X.structureMap :=
  pullback.lift (FixedNodeHom.markedEvaluation P p H)
    (FixedNodeHom.markedEvaluation P q H) (by
      rw [FixedNodeHom.markedEvaluation_overC,
        FixedNodeHom.markedEvaluation_overC])

theorem pairedEvaluation_first :
    pairedEvaluation P p q H ≫ firstProjection X.structureMap =
      FixedNodeHom.markedEvaluation P p H :=
  pullback.lift_fst _ _ _

theorem pairedEvaluation_second :
    pairedEvaluation P p q H ≫ secondProjection X.structureMap =
      FixedNodeHom.markedEvaluation P q H :=
  pullback.lift_snd _ _ _

theorem pairedEvaluation_overC :
    pairedEvaluation P p q H ≫ (firstProjection X.structureMap ≫ X.structureMap) =
      H.toC := by
  rw [← Category.assoc, pairedEvaluation_first, FixedNodeHom.markedEvaluation_overC]

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "FIXED_MARKINGS_STAGE EXIT_PAIR"
  err.putStrLn "FIXED_MARKINGS_STAGE ENTER_SECTION"
  err.flush

/-- Keep both markings fixed and vary the actual open Hom parameter. -/
def markingSection : U.toScheme ⟶ HomTwoPointEvaluation.Source P H U :=
  pullback.lift ((U.ι ≫ H.toC) ≫ pairMap P p q) (𝟙 U.toScheme) (by
    simp only [Category.assoc, pairMap_overC, Category.comp_id, Category.id_comp])

theorem markingSection_fst :
    markingSection P p q H U ≫
      pullback.fst (HomTwoPointEvaluation.squareStructure P) (U.ι ≫ H.toC) =
      (U.ι ≫ H.toC) ≫ pairMap P p q :=
  pullback.lift_fst _ _ _

theorem markingSection_snd :
    markingSection P p q H U ≫
      pullback.snd (HomTwoPointEvaluation.squareStructure P) (U.ι ≫ H.toC) =
      𝟙 U.toScheme :=
  pullback.lift_snd _ _ _

theorem markingSection_overC :
    markingSection P p q H U ≫ HomTwoPointEvaluation.structureMap P H U =
      U.ι ≫ H.toC := by
  simp only [markingSection, HomTwoPointEvaluation.structureMap,
    pullback.lift_snd_assoc, Category.id_comp]

theorem markingSection_leftSource :
    markingSection P p q H U ≫ HomTwoPointEvaluation.leftSource P H U =
      U.ι ≫ FixedNodeHom.markingSection P p H.toC := by
  apply pullback.hom_ext
  · simp only [Category.assoc, HomTwoPointEvaluation.leftSource,
      pullback.lift_fst, FixedNodeHom.markingSection_fst]
    rw [← Category.assoc, markingSection_fst]
    simp only [Category.assoc, pairMap_first]
  · simp only [Category.assoc, HomTwoPointEvaluation.leftSource,
      pullback.lift_snd, FixedNodeHom.markingSection_snd, Category.comp_id]
    rw [← Category.assoc, markingSection_snd, Category.id_comp]

theorem markingSection_rightSource :
    markingSection P p q H U ≫ HomTwoPointEvaluation.rightSource P H U =
      U.ι ≫ FixedNodeHom.markingSection P q H.toC := by
  apply pullback.hom_ext
  · simp only [Category.assoc, HomTwoPointEvaluation.rightSource,
      pullback.lift_fst, FixedNodeHom.markingSection_fst]
    rw [← Category.assoc, markingSection_fst]
    simp only [Category.assoc, pairMap_second]
  · simp only [Category.assoc, HomTwoPointEvaluation.rightSource,
      pullback.lift_snd, FixedNodeHom.markingSection_snd, Category.comp_id]
    rw [← Category.assoc, markingSection_snd, Category.id_comp]

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "FIXED_MARKINGS_STAGE EXIT_SECTION"
  err.putStrLn "FIXED_MARKINGS_STAGE ENTER_EVALUATION"
  err.flush

theorem markingSection_evaluation_first :
    (markingSection P p q H U ≫ HomTwoPointEvaluation.evaluation P H U) ≫
      firstProjection X.structureMap = U.ι ≫ FixedNodeHom.markedEvaluation P p H := by
  rw [Category.assoc, HomTwoPointEvaluation.evaluation_first]
  simpa only [Category.assoc, FixedNodeHom.markedEvaluation] using
    congrArg (fun m => m ≫ H.evaluation) (markingSection_leftSource P p q H U)

theorem markingSection_evaluation_second :
    (markingSection P p q H U ≫ HomTwoPointEvaluation.evaluation P H U) ≫
      secondProjection X.structureMap = U.ι ≫ FixedNodeHom.markedEvaluation P q H := by
  rw [Category.assoc, HomTwoPointEvaluation.evaluation_second]
  simpa only [Category.assoc, FixedNodeHom.markedEvaluation] using
    congrArg (fun m => m ≫ H.evaluation) (markingSection_rightSource P p q H U)

theorem markingSection_evaluation :
    markingSection P p q H U ≫ HomTwoPointEvaluation.evaluation P H U =
      U.ι ≫ pairedEvaluation P p q H := by
  apply pullback.hom_ext
  · change (markingSection P p q H U ≫ HomTwoPointEvaluation.evaluation P H U) ≫
      firstProjection X.structureMap =
      (U.ι ≫ pairedEvaluation P p q H) ≫ firstProjection X.structureMap
    rw [markingSection_evaluation_first, Category.assoc, pairedEvaluation_first]
  · change (markingSection P p q H U ≫ HomTwoPointEvaluation.evaluation P H U) ≫
      secondProjection X.structureMap =
      (U.ι ≫ pairedEvaluation P p q H) ≫ secondProjection X.structureMap
    rw [markingSection_evaluation_second, Category.assoc, pairedEvaluation_second]

/-- The literal paired map on the open, with no parameter-scheme abbreviation. -/
theorem markingSection_evaluation_lift :
    markingSection P p q H U ≫ HomTwoPointEvaluation.evaluation P H U =
      pullback.lift (U.ι ≫ FixedNodeHom.markedEvaluation P p H)
        (U.ι ≫ FixedNodeHom.markedEvaluation P q H) (by
          simp only [Category.assoc, FixedNodeHom.markedEvaluation_overC]) := by
  apply pullback.hom_ext
  · simpa only [pullback.lift_fst, firstProjection] using
      markingSection_evaluation_first P p q H U
  · simpa only [pullback.lift_snd, secondProjection] using
      markingSection_evaluation_second P p q H U

/-- This applies equally to complex parameters and whole nonreduced test maps. -/
def liftParameter {T : Scheme} (sT : T ⟶ ComplexBase)
    (t : PointsOver T sT U.toScheme (U.ι ≫ H.toC)) :
    PointsOver T sT (HomTwoPointEvaluation.Source P H U)
      (HomTwoPointEvaluation.structureMap P H U) :=
  ⟨t.val ≫ markingSection P p q H U, by
    rw [Category.assoc, markingSection_overC, t.property]⟩

/-- Density of the fixed-pair map already forces density of the full evaluation. -/
theorem denseRange_of_markedPair
    (h : DenseRange (U.ι ≫ pairedEvaluation P p q H).base) :
    DenseRange (HomTwoPointEvaluation.evaluation P H U).base := by
  have hc : DenseRange
      (markingSection P p q H U ≫ HomTwoPointEvaluation.evaluation P H U).base := by
    rw [markingSection_evaluation]
    exact h
  exact DenseRange.of_comp (g := (markingSection P p q H U).base) hc

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "FIXED_MARKINGS_STAGE EXIT_EVALUATION"
  err.putStrLn "FIXED_MARKINGS_COMPLETE"
  err.flush

#print axioms pairedEvaluation
#print axioms pairedEvaluation_overC
#print axioms markingSection
#print axioms markingSection_overC
#print axioms markingSection_leftSource
#print axioms markingSection_rightSource
#print axioms markingSection_evaluation_first
#print axioms markingSection_evaluation_second
#print axioms markingSection_evaluation
#print axioms markingSection_evaluation_lift
#print axioms liftParameter
#print axioms denseRange_of_markedPair

end LeBrunSalamon.Next3i.FixedMarkings
end
