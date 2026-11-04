import LSNodalConic
import LSNodalFixedEnds
import LSProjectiveTransport
import LSSuitablePair

/-!
# Assembly of the actual smoothing construction

The finite-dimensional endpoint targets come from their actual open
immersions into the smooth contact variety. The original smoothing
interface is filled by the individual geometric theorems, and its
conic is transported to every permitted projective-line source model.
The suitable-pair and fixed-end arguments are ordinary proofs in the
imported construction modules.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.PhaseThirtyFive LeBrunSalamon.Core LeBrunSalamon.Skeleton

namespace LeBrunSalamon.Construction.Smoothing

open Lines

/-- The two actual endpoint charts have finite-dimensional tangent
spaces because their maps to Spec C are locally of finite presentation. -/
theorem endpointTangent_finite {n : ℕ} {X : ContactFanoManifold n}
    {D : SuitablePair X} (G : Germ D) :
    FiniteDimensional ℂ (G.firstTarget.Tangent × G.secondTarget.Tangent) := by
  letI : IsOpenImmersion G.firstOpen := G.firstOpen_immersion
  letI : IsOpenImmersion G.secondOpen := G.secondOpen_immersion
  have h₁ : LocallyOfFinitePresentation G.firstTarget.toC := by
    rw [← G.firstOpen_over]
    infer_instance
  have h₂ : LocallyOfFinitePresentation G.secondTarget.toC := by
    rw [← G.secondOpen_over]
    infer_instance
  letI := Charts.tangent_finite_of_lfp G.firstTarget h₁
  letI := Charts.tangent_finite_of_lfp G.secondTarget h₂
  infer_instance

/-- Every field is supplied by the corresponding actual construction;
the original final conic target is not used in this constructor. -/
theorem constructedInputs : Inputs :=
  { suitable := fun _ X hp => suitablePair_exists X hp
    germ := fun _ _ D => germ_exists D
    linearFacts := fun _ _ _ G =>
      ⟨endpointTangent_finite G, germ_baseDifferential_surjective G,
        germ_verticalDefectOne G⟩
    fixedEnds := fun _ _ _ G => germ_noFixedEnds G
    extract := fun _ _ _ G hb he => germ_extracts_veryFreeConic G hb he }

theorem primitiveSmoothing : PrimitiveSmoothing P marking :=
  constructedInputs.assemble

/-- Degree and two-point interpolation are transported by an actual
projective-line isomorphism over C, including its tangent differential. -/
theorem primitiveSmoothing_everySource (Q : ProjectiveLineOverC)
    (q : ProjectiveLinePoint Q) : PrimitiveSmoothing Q q := by
  intro n X hp
  obtain ⟨g⟩ := primitiveSmoothing n X hp
  exact ⟨ProjectiveTransport.conicBetweenModels Q P q marking g⟩

end LeBrunSalamon.Construction.Smoothing

namespace LeBrunSalamon.PhaseThirtyFive

/-- PROJECT TARGET: the major contact-line smoothing theorem. This assertion must be proved from an actual
nodal family and the relative Hom deformation theory; the numerical dimension count does not prove it. -/
theorem primitiveContactFano_veryFreeConic_target
    (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) {n : ℕ}
    (X : ContactFanoManifold n) (hPic : HasPrimitiveContactPicard X.contact) :
    ∃ f : RationalCurve P X.variety,
      IsIntrinsicContactConic P p X.contact f ∧
      IsVeryFreeRationalCurve P X.variety (intrinsicTangentBundle X.variety) f := by
  exact (veryFreeConic_nonempty_iff P p X).mp
    (Construction.Smoothing.primitiveSmoothing_everySource P p n X hPic)

end LeBrunSalamon.PhaseThirtyFive

end

#print axioms LeBrunSalamon.PhaseThirtyFive.primitiveContactFano_veryFreeConic_target
