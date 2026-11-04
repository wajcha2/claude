import RecompileSections

/-! Actual global polynomial vector fields used in the source bivector.
This file has no admitted input. The reciprocal-coordinate sign is retained. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.P1Charts LeBrunSalamon.P1TwistFrames
open LeBrunSalamon.LocalFrames LeBrunSalamon.TwoChartSections
open LeBrunSalamon.P1TangentTranslation
open scoped LaurentPolynomial

namespace LeBrunSalamon.P1TangentSections

def polynomialCoordinates (P : ProjectiveLineOverC) (i : Fin 2) :
    SectionsOn (tangentSheaf P.structureMap) (chartOpen i) ≃+ Polynomial ℂ :=
  (coordinates (derivativeFrame P i)).toAddEquiv.trans
    (polynomialChartRingEquiv i).toAddEquiv

def reversedCoordinates (P : ProjectiveLineOverC) :
    SectionsOn (tangentSheaf P.structureMap) (chartOpen 1) ≃+ Polynomial ℂ :=
  (polynomialCoordinates P 1).trans (AddEquiv.neg (Polynomial ℂ))

def laurentCoordinates (P : ProjectiveLineOverC) :
    SectionsOn (tangentSheaf P.structureMap) overlap ≃+ ℂ[T;T⁻¹] :=
  (coordinates (frameZero P)).toAddEquiv.trans overlapRingCoordinates.toAddEquiv

theorem ring_restriction_zero (a : RingSections ProjectiveLine (chartOpen 0)) :
    overlapRingCoordinates (ProjectiveLine.presheaf.map
      (homOfLE inf_le_left).op a) = (polynomialChartRingEquiv 0 a).toLaurent := by
  have h := congrArg (fun f : Polynomial ℂ →+* ℂ[T;T⁻¹] =>
    f (polynomialChartRingEquiv 0 a)) zeroRestrictionRingHom_eq_toLaurent
  change overlapRingCoordinates (ProjectiveLine.presheaf.map (homOfLE inf_le_left).op
    ((polynomialChartRingEquiv 0).symm (polynomialChartRingEquiv 0 a))) = _ at h
  rwa [RingEquiv.symm_apply_apply] at h

theorem ring_restriction_one (a : RingSections ProjectiveLine (chartOpen 1)) :
    overlapRingCoordinates (ProjectiveLine.presheaf.map
      (homOfLE inf_le_right).op a) =
        LaurentPolynomial.invert (polynomialChartRingEquiv 1 a).toLaurent := by
  have h := congrArg (fun f : Polynomial ℂ →+* ℂ[T;T⁻¹] =>
    f (polynomialChartRingEquiv 1 a)) oneRestrictionRingHom_eq_invert_toLaurent
  change overlapRingCoordinates (ProjectiveLine.presheaf.map (homOfLE inf_le_right).op
    ((polynomialChartRingEquiv 1).symm (polynomialChartRingEquiv 1 a))) = _ at h
  rwa [RingEquiv.symm_apply_apply] at h

theorem restrict_zero (P : ProjectiveLineOverC)
    (v : SectionsOn (tangentSheaf P.structureMap) (chartOpen 0)) :
    laurentCoordinates P (restrictValue (tangentSheaf P.structureMap) inf_le_left v) =
      (polynomialCoordinates P 0 v).toLaurent := by
  change overlapRingCoordinates
    (coordinates (restrict (homOfLE inf_le_left) (derivativeFrame P 0))
      ((tangentSheaf P.structureMap).presheaf.map (homOfLE inf_le_left).op v)) = _
  rw [coordinates_restrict]
  exact ring_restriction_zero (coordinates (derivativeFrame P 0) v)

theorem restrict_one (P : ProjectiveLineOverC)
    (v : SectionsOn (tangentSheaf P.structureMap) (chartOpen 1)) :
    laurentCoordinates P (restrictValue (tangentSheaf P.structureMap) inf_le_right v) =
      LaurentPolynomial.invert (reversedCoordinates P v).toLaurent *
        LaurentPolynomial.T 2 := by
  change overlapRingCoordinates (coordinates (frameZero P)
    ((tangentSheaf P.structureMap).presheaf.map (homOfLE inf_le_right).op v)) = _
  rw [coordinates_change (frameZero P) (frameOne P), map_mul, derivative_transition]
  change overlapRingCoordinates
    (coordinates (restrict (homOfLE inf_le_right) (derivativeFrame P 1))
      ((tangentSheaf P.structureMap).presheaf.map (homOfLE inf_le_right).op v)) *
        -LaurentPolynomial.T 2 = _
  rw [coordinates_restrict]
  rw [ring_restriction_one]
  change LaurentPolynomial.invert (polynomialCoordinates P 1 v).toLaurent *
      -LaurentPolynomial.T 2 =
    LaurentPolynomial.invert (-polynomialCoordinates P 1 v).toLaurent *
      LaurentPolynomial.T 2
  rw [map_neg, map_neg, mul_neg, neg_mul]

def matchingEquiv (P : ProjectiveLineOverC) :
    AlgebraicSection (tangentSheaf P.structureMap) ≃+
      P1Overlap.matchingSpace (K := ℂ) 2 :=
  algebraicSectionsLaurentEquiv (tangentSheaf P.structureMap)
    (chartOpen 0) (chartOpen 1) 2
    (polynomialCoordinates P 0) (reversedCoordinates P) (laurentCoordinates P)
    (restrict_zero P) (restrict_one P) chartOpen_zero_sup_one

theorem matchingEquiv_zero (P : ProjectiveLineOverC)
    (v : AlgebraicSection (tangentSheaf P.structureMap)) :
    (matchingEquiv P v).val.1 = polynomialCoordinates P 0
      (restrictValue (tangentSheaf P.structureMap) (show chartOpen 0 ≤ ⊤ from le_top)
        (sectionValue v)) := rfl

theorem matchingEquiv_one (P : ProjectiveLineOverC)
    (v : AlgebraicSection (tangentSheaf P.structureMap)) :
    (matchingEquiv P v).val.2 = -polynomialCoordinates P 1
      (restrictValue (tangentSheaf P.structureMap) (show chartOpen 1 ≤ ⊤ from le_top)
        (sectionValue v)) := rfl

/-- The degree-two matching pair for the kth polynomial vector field. -/
def monomialPair (k : Fin 3) : P1Overlap.matchingSpace (K := ℂ) 2 :=
  ⟨(Polynomial.X ^ k.val, Polynomial.X ^ (2 - k.val)), by
    change (Polynomial.X ^ k.val : Polynomial ℂ).toLaurent =
      LaurentPolynomial.invert (Polynomial.X ^ (2 - k.val) : Polynomial ℂ).toLaurent *
        LaurentPolynomial.T 2
    rw [map_pow, Polynomial.toLaurent_X, map_pow, Polynomial.toLaurent_X,
      map_pow, LaurentPolynomial.invert_T, LaurentPolynomial.T_pow,
      LaurentPolynomial.T_pow, ← LaurentPolynomial.T_add]
    congr 1
    have hk := k.isLt
    omega⟩

def polynomialField (P : ProjectiveLineOverC) (k : Fin 3) :
    AlgebraicSection (tangentSheaf P.structureMap) :=
  (matchingEquiv P).symm (monomialPair k)

theorem polynomialField_zero (P : ProjectiveLineOverC) (k : Fin 3) :
    polynomialCoordinates P 0
      (restrictValue (tangentSheaf P.structureMap) (show chartOpen 0 ≤ ⊤ from le_top)
        (sectionValue (polynomialField P k))) = Polynomial.X ^ k.val := by
  rw [← matchingEquiv_zero]
  exact congrArg (fun a : P1Overlap.matchingSpace (K := ℂ) 2 => a.val.1)
    ((matchingEquiv P).apply_symm_apply (monomialPair k))

theorem polynomialField_one (P : ProjectiveLineOverC) (k : Fin 3) :
    polynomialCoordinates P 1
      (restrictValue (tangentSheaf P.structureMap) (show chartOpen 1 ≤ ⊤ from le_top)
        (sectionValue (polynomialField P k))) = -(Polynomial.X ^ (2 - k.val)) := by
  have h := congrArg (fun a : P1Overlap.matchingSpace (K := ℂ) 2 => a.val.2)
    ((matchingEquiv P).apply_symm_apply (monomialPair k))
  change -(polynomialCoordinates P 1
    (restrictValue (tangentSheaf P.structureMap) (show chartOpen 1 ≤ ⊤ from le_top)
      (sectionValue (polynomialField P k)))) = Polynomial.X ^ (2 - k.val) at h
  exact neg_eq_iff_eq_neg.mp h

end LeBrunSalamon.P1TangentSections

end
