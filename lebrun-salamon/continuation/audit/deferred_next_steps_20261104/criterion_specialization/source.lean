import LSChartSmoothnessCriteria
import LSHomTwoPointDominanceCompositionProbe

/-! Exact complex specialization of the existing3h generic criterion.
The native generic helper is an independently verified, separate import.
No new published declaration or geometric hypothesis is introduced.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option profiler true
set_option stderrAsMessages false
set_option maxErrors 1

open CategoryTheory AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.Core LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.Next3i.ComplexCriterionSpecialization

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "COMPLEX_CRITERION_STAGE ENTER_DUAL"
  err.flush

theorem dualScheme_eq :
    Spec (CommRingCat.of (DualNumberGeometry.Dual ℂ)) = Infinitesimal.DualScheme := rfl

theorem dualToBase_eq :
    DualNumberGeometry.dualToBase ℂ = Infinitesimal.dualToC := rfl

theorem origin_eq :
    DualNumberGeometry.origin ℂ = Infinitesimal.origin := rfl

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "COMPLEX_CRITERION_STAGE EXIT_DUAL"
  err.putStrLn "COMPLEX_CRITERION_STAGE ENTER_SPECIALIZATION"
  err.flush

/-- Every map, center equation, neighborhood, and smoothness premise is retained. -/
theorem complexCriterion_of_generic
    (h : DualNumberGeometry.RationalPointDifferentialCriterion) :
    TwoPointDominance.ComplexTangentLiftCriterion := by
  intro A B sA sB F hF a ha hA hB hlifts
  apply h ℂ A B sA sB F hF a ha hA hB
  intro b hb hb0
  rw [dualToBase_eq] at hb
  rw [origin_eq] at hb0
  obtain ⟨l, hl, hl0, hlF⟩ := hlifts b hb hb0
  refine ⟨l, ?_, ?_, hlF⟩
  · simpa only [dualToBase_eq] using hl
  · simpa only [origin_eq] using hl0

/-- Apply precisely the existing3h published leaf after the proved translation. -/
theorem complexCriterion : TwoPointDominance.ComplexTangentLiftCriterion :=
  complexCriterion_of_generic
    @PublishedInputs.Smoothness.smooth_of_surjective_tangent_lifts

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "COMPLEX_CRITERION_STAGE EXIT_SPECIALIZATION"
  err.putStrLn "COMPLEX_CRITERION_COMPLETE"
  err.flush

#print axioms dualScheme_eq
#print axioms dualToBase_eq
#print axioms origin_eq
#print axioms complexCriterion_of_generic
#print axioms complexCriterion

end LeBrunSalamon.Next3i.ComplexCriterionSpecialization
end
