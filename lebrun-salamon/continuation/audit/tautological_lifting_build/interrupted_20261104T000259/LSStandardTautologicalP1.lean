import LSStandardTautological

/-!
Actual comparison of the standard homogeneous tautological sheaf on P1
with the project's marked-point twist.  Its transition is computed through
the existing homogeneous-localization, polynomial, and Laurent charts.
The resulting isomorphism is obtained by sheaf gluing.  No theorem in this
file is admitted.  Off-graph candidate; native verification is pending.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option maxErrors 1

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.P1Charts LeBrunSalamon.P1TwistFrames
open LeBrunSalamon.LocalFrames
open scoped LaurentPolynomial

namespace LeBrunSalamon.StandardTautologicalP1

abbrev tautologicalLine : LineBundle ProjectiveLine := StandardTautological.line ℂ 1

def chartFrame (i : Fin 2) : OverFrame tautologicalLine.sheaf (chartOpen i) :=
  StandardTautological.frame ℂ 1 i

def coordinateSection (j : Fin 2) : AlgebraicSection tautologicalLine.sheaf :=
  StandardTautological.coordinate ℂ 1 j

/-- Standard homogeneous coordinates, expressed in the already constructed
polynomial chart rings, are 1 and the actual affine coordinate. -/
theorem polynomial_coefficient (i j : Fin 2) :
    polynomialChartRingEquiv i
      (coordinates (chartFrame i)
        (Scheme.Modules.Hom.app (coordinateSection j) (chartOpen i)
          (1 : RingSections ProjectiveLine (chartOpen i)))) =
      if j = i then 1 else Polynomial.X := by
  have h := StandardTautological.section_coordinates ℂ 1 i j
  change coordinates (chartFrame i)
    (Scheme.Modules.Hom.app (coordinateSection j) (chartOpen i)
      (1 : RingSections ProjectiveLine (chartOpen i))) =
        (chartSectionsIso i).hom (P1Charts.ratio i j) at h
  rw [h]
  change chartRingEquiv i
    ((chartSectionsIso i).inv ((chartSectionsIso i).hom (P1Charts.ratio i j))) = _
  rw [Iso.hom_inv_id_apply]
  exact chartToPolynomial_ratio i j

theorem generator_eq_coordinate (i : Fin 2) :
    generator (chartFrame i) =
      Scheme.Modules.Hom.app (coordinateSection i) (chartOpen i)
        (1 : RingSections ProjectiveLine (chartOpen i)) := by
  apply (coordinates (chartFrame i)).injective
  rw [coordinates_generator]
  apply (polynomialChartRingEquiv i).injective
  rw [map_one, polynomial_coefficient]
  simp

/-- Restriction is the original sheaf map of the specified global section. -/
private theorem section_restrict {X : Scheme} {E : X.Modules}
    (a : AlgebraicSection E) {U V : X.Opens} (i : V ⟶ U) :
    E.presheaf.map i.op
      (Scheme.Modules.Hom.app a U (1 : RingSections X U)) =
      Scheme.Modules.Hom.app a V (1 : RingSections X V) := by
  have h := sheafHom_naturality a i (1 : RingSections X U)
  change E.presheaf.map i.op
      (Scheme.Modules.Hom.app a U (1 : RingSections X U)) =
    Scheme.Modules.Hom.app a V (X.presheaf.map i.op (1 : RingSections X U)) at h
  simpa only [map_one] using h

/-- The actual overlap transition is the restriction of X1/X0. -/
theorem transition_eq_restriction :
    transition (restrict (homOfLE inf_le_left) (chartFrame 0))
      (restrict (homOfLE inf_le_right) (chartFrame 1)) =
    ProjectiveLine.presheaf.map (homOfLE inf_le_left).op
      (coordinates (chartFrame 0)
        (Scheme.Modules.Hom.app (coordinateSection 1) (chartOpen 0)
          (1 : RingSections ProjectiveLine (chartOpen 0)))) := by
  change coordinates (restrict (homOfLE inf_le_left) (chartFrame 0))
    (generator (restrict (homOfLE inf_le_right) (chartFrame 1))) = _
  rw [← generator_restrict, generator_eq_coordinate, section_restrict]
  rw [← section_restrict (coordinateSection 1)
    (homOfLE (inf_le_left : chartOpen 0 ⊓ chartOpen 1 ≤ chartOpen 0))]
  exact coordinates_restrict _ _ _

/-- The coefficient is exactly T, with no undetermined scalar and the
correct orientation for the marked O(1) frames. -/
theorem transition_laurent :
    overlapRingCoordinates
      (transition (restrict (homOfLE inf_le_left) (chartFrame 0))
        (restrict (homOfLE inf_le_right) (chartFrame 1))) =
      LaurentPolynomial.T 1 := by
  rw [transition_eq_restriction]
  let a := coordinates (chartFrame 0)
    (Scheme.Modules.Hom.app (coordinateSection 1) (chartOpen 0)
      (1 : RingSections ProjectiveLine (chartOpen 0)))
  have ha : polynomialChartRingEquiv 0 a = Polynomial.X := by
    simpa [a] using polynomial_coefficient 0 1
  change overlapRingCoordinates
    (ProjectiveLine.presheaf.map (homOfLE inf_le_left).op a) = _
  calc
    _ = zeroRestrictionRingHom (polynomialChartRingEquiv 0 a) := by
      change _ = overlapRingCoordinates
        (ProjectiveLine.presheaf.map (homOfLE inf_le_left).op
          ((polynomialChartRingEquiv 0).symm (polynomialChartRingEquiv 0 a)))
      rw [RingEquiv.symm_apply_apply]
    _ = zeroRestrictionRingHom Polynomial.X := congrArg zeroRestrictionRingHom ha
    _ = LaurentPolynomial.T 1 := by
      rw [zeroRestrictionRingHom_eq_toLaurent, Polynomial.toLaurent_X]

/-- The actual standard homogeneous tautological line is the project's
actual marked-point O(1), by compatible chart frames and sheaf gluing. -/
def markedOneIso (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) :
    tautologicalLine.sheaf ≅ (projectiveTwist P p 1).sheaf :=
  P1PicardTranslation.isoOfTransition (chartOpen 0) (chartOpen 1)
    chartOpen_zero_sup_one (chartFrame 0) (chartFrame 1)
    (twistOverFrame P p 1 0) (twistOverFrame P p 1 1) (by
      apply overlapRingCoordinates.injective
      change overlapRingCoordinates
        (transition (restrict (homOfLE inf_le_left) (chartFrame 0))
          (restrict (homOfLE inf_le_right) (chartFrame 1))) =
        (laurentTransitionUnit P p 1 : ℂ[T;T⁻¹])
      rw [transition_laurent, laurentTransitionUnit_eq_T])

/-- Degree one is deduced from the actual sheaf isomorphism, not from a
label on the arbitrary universal quotient. -/
theorem degree_one (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) :
    projectiveLineDegree P p tautologicalLine = 1 := by
  rw [projectiveLineDegree_iso P p tautologicalLine (projectiveTwist P p 1)
    (markedOneIso P p), projectiveTwist_degree]

end LeBrunSalamon.StandardTautologicalP1

end
