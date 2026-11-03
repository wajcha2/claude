import LSContactDirections

/-!
## Published general-point contact-direction geometry

The two explicitly reviewed leaves below retain the corrected published
scope: the whole union spans; the smooth Legendrian direction theorem
has n>=2. The ordinary consumers construct the actual Hom families,
prove cone-addition dominance, and extract the suitable pair.

Primary sources and the exact dictionary to actual cone quotient rings
are recorded in owners/nodal/VMRT_GEOMETRY_PROPOSAL.lean.txt and
VMRT_GEOMETRY_RECORD.json. These are standard geometric corollaries,
not verbatim statements in the project's vocabulary.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.Lines.PublishedDirections

open DirectionCones VelocityCoordinates

/-- Standard affine formulation of a smooth Legendrian project's
component cones, using actual polynomial quotient rings and derivations. -/
def SmoothIsotropicConeCharts {n : ℕ} (X : ContactFanoManifold n)
    (x : ComplexPoint X.variety) (C : GlobalVelocity.TargetChart X.variety x)
    (D : ReducedProjectiveDirections (dimension (n := n))) : Prop :=
  ∀ (K : D.Component)
    (p : CoordinateRing (D.componentConePoints (contactFrame X x C) K) →ₐ[ℂ] ℂ),
    (fun i => p (coordinate (D.componentConePoints (contactFrame X x C) K) i)) ≠ 0 →
      ∃ u : CoordinateRing (D.componentConePoints (contactFrame X x C) K),
        p u ≠ 0 ∧ Algebra.FormallySmooth ℂ (Localization.Away u) ∧
          ∀ (z : Localization.Away u →ₐ[ℂ] ℂ)
            (a b : Infinitesimal.Tangent (Localization.Away u) z),
            ConePairing.pairing (omega X x C)
              (fun i => a.val (ConeRadial.localizedCoordinate (L := Localization.Away u)
                (D.componentConePoints (contactFrame X x C) K) i))
              (fun i => b.val (ConeRadial.localizedCoordinate (L := Localization.Away u)
                (D.componentConePoints (contactFrame X x C) K) i)) = 0

/-- The geometric content of the corrected published VMRT theorem.
The ambient coordinates are already normalized on intrinsic contact
vectors and on the original Levi form. -/
structure LegendrianDirections {n : ℕ} (X : ContactFanoManifold n)
    (x : ComplexPoint X.variety) (C : GlobalVelocity.TargetChart X.variety x) where
  directions : ReducedProjectiveDirections (dimension (n := n))
  realizes : RealizesSelectedDirections (fun _ : FreeLine X => True) x
    (contactFrame X x C) directions
  smooth : Smooth directions.toC
  disjoint : Pairwise (fun K E : directions.Component => Disjoint K.val E.val)
  cone_closed : ∀ K : directions.Component,
    EquationClosed (directions.componentConePoints (contactFrame X x C) K)
  cone_integral : ∀ K : directions.Component,
    IsDomain (CoordinateRing (directions.componentConePoints (contactFrame X x C) K))
  cone_dimension : ∀ K : directions.Component,
    ringKrullDim (CoordinateRing (directions.componentConePoints (contactFrame X x C) K)) =
      (n : WithBot ℕ∞)
  cone_charts : SmoothIsotropicConeCharts X x C directions

namespace StandardInputs

/-- Union-spanning theorem, with no dimension-three classification input.
Only directions of actual free degree-one maps are selected. -/
theorem general_selectedDirections_span {n : ℕ} (X : ContactFanoManifold n)
    (hPic : HasPrimitiveContactPicard X.contact) :
    ∃ U : X.variety.scheme.Opens,
      Dense (U : Set X.variety.scheme) ∧
        ∀ x : ComplexPoint X.variety,
          x.map (IsLocalRing.closedPoint ℂ) ∈ U →
            Submodule.span ℂ
              (projectiveCone (selectedDirections (fun _ : FreeLine X => True) x)) = ⊤ := by
  sorry

/-- Corrected smooth Legendrian direction theorem, with explicit n>=2.
The three-dimensional branch uses the preceding spanning theorem and
the existing ordinary two-dimensional symplectic argument. -/
theorem general_legendrianDirections {n : ℕ} (X : ContactFanoManifold n)
    (hn : 2 ≤ n) (hPic : HasPrimitiveContactPicard X.contact) :
    ∃ U : X.variety.scheme.Opens,
      Dense (U : Set X.variety.scheme) ∧
        ∀ x : ComplexPoint X.variety,
          x.map (IsLocalRing.closedPoint ℂ) ∈ U →
            ∀ C : GlobalVelocity.TargetChart X.variety x,
              Nonempty (LegendrianDirections X x C) := by
  sorry

end StandardInputs
end LeBrunSalamon.Construction.Lines.PublishedDirections

end
