import LSP1PicardTranslation
import LSAffineDerivations

/-! Actual derivative frames and their transition on the two polynomial
charts of the projective line. This file adds no published input. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.P1Charts LeBrunSalamon.P1TwistFrames
open LeBrunSalamon.LocalFrames LeBrunSalamon.P1PicardTranslation
open LeBrunSalamon.Skeleton
open scoped LaurentPolynomial

namespace LeBrunSalamon.P1TangentTranslation

def transportedDerivative {R : Type*} [CommRing R] (e : R ≃+* Polynomial ℂ)
    (a : R) : R := e.symm (e a).derivative

theorem transportedDerivative_zero {R : Type*} [CommRing R]
    (e : R ≃+* Polynomial ℂ) : transportedDerivative e 0 = 0 := by
  simp only [transportedDerivative, map_zero, Polynomial.derivative_zero]

theorem transportedDerivative_add {R : Type*} [CommRing R]
    (e : R ≃+* Polynomial ℂ) (a b : R) :
    transportedDerivative e (a + b) =
      transportedDerivative e a + transportedDerivative e b := by
  simp only [transportedDerivative, map_add, Polynomial.derivative_add]

theorem transportedDerivative_mul {R : Type*} [CommRing R]
    (e : R ≃+* Polynomial ℂ) (a b : R) :
    transportedDerivative e (a * b) =
      a * transportedDerivative e b + b * transportedDerivative e a := by
  simp only [transportedDerivative, map_mul, Polynomial.derivative_mul,
    map_add, RingEquiv.symm_apply_apply]
  ac_rfl

theorem derivation_reciprocal {R : Type*} [CommRing R]
    (D : R → R) (hmul : ∀ a b, D (a * b) = a * D b + b * D a)
    (z w : R) (hzw : z * w = 1) (hw : D w = 1) : D z = -(z ^ 2) := by
  have h1 : D 1 = 0 := by
    have h := hmul 1 1
    simp only [one_mul] at h
    linear_combination -h
  have h := hmul z w
  rw [hzw, h1, hw, mul_one] at h
  have hz := congrArg (fun a : R => z * a) h
  rw [mul_zero, mul_add, ← mul_assoc, hzw, one_mul] at hz
  linear_combination -hz

theorem unit_of_left_inverse {R : Type*} [CommRing R] (a b : R)
    (h : a * b = 1) : IsUnit b := by
  refine ⟨⟨b, a, ?_, h⟩, rfl⟩
  rw [mul_comm]
  exact h

def tangentLine (P : ProjectiveLineOverC) : LineBundle ProjectiveLine :=
  ⟨tangentSheaf P.structureMap,
    smooth_tangent_rank P.structureMap 1 (CotangentTwistProof.structureMap_smooth P)⟩

def coordinate (i : Fin 2) : RingSections ProjectiveLine (chartOpen i) :=
  (polynomialChartRingEquiv i).symm Polynomial.X

/-- A change of the supplied complex base isomorphism still maps constants
to constant polynomials on each actual affine chart. -/
theorem base_constants_polynomial (P : ProjectiveLineOverC) (i : Fin 2) (c : ℂ) :
    ∃ d : ℂ, polynomialChartRingEquiv i (complexConstant P.structureMap (chartOpen i) c) =
      Polynomial.C d := by
  let A := CotangentTwistProof.baseChangeIso P
  let d := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
    (A.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))
  refine ⟨d, ?_⟩
  have hd : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv d =
      A.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c) :=
    Iso.hom_inv_id_apply _ _
  rw [complexConstant, ← CotangentTwistProof.baseMap_factor P,
    Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply]
  rw [← hd]
  exact polynomialChartRingEquiv_canonical_constant i d

/-- The ordinary polynomial derivative realizes an actual local tangent
section, for every allowed complex base map. -/
theorem coordinate_vector_exists (P : ProjectiveLineOverC) (i : Fin 2) :
    ∃ v : SectionsOn (tangentSheaf P.structureMap) (chartOpen i),
      tangentActs P.structureMap (chartOpen i) v (coordinate i) = 1 := by
  let e := polynomialChartRingEquiv i
  let D := transportedDerivative e
  obtain ⟨v, hv⟩ := TangentAffine.affine_tangent_action_exists P.structureMap
    (chartOpen i) (chartOpen_affine i) D
    (transportedDerivative_zero e)
    (transportedDerivative_add e)
    (transportedDerivative_mul e)
    (by
      intro c
      obtain ⟨d, hd⟩ := base_constants_polynomial P i c
      change e.symm (e (complexConstant P.structureMap (chartOpen i) c)).derivative = 0
      rw [hd, Polynomial.derivative_C, map_zero])
  refine ⟨v, ?_⟩
  rw [hv]
  change e.symm (e (e.symm Polynomial.X)).derivative = 1
  rw [RingEquiv.apply_symm_apply, Polynomial.derivative_X, map_one]

/-- A chosen frame's derivative coefficient is an actual unit, since d/dz
exists and every vector is its frame coordinate times the frame generator. -/
theorem frame_coordinate_unit (P : ProjectiveLineOverC) (i : Fin 2)
    (e : OverFrame (tangentSheaf P.structureMap) (chartOpen i)) :
    IsUnit (tangentActs P.structureMap (chartOpen i) (generator e) (coordinate i)) := by
  obtain ⟨v, hv⟩ := coordinate_vector_exists P i
  have hmul : coordinates e v *
      tangentActs P.structureMap (chartOpen i) (generator e) (coordinate i) = 1 := by
    rw [← TangentActionProof.smul_field, reconstruct]
    exact hv
  exact unit_of_left_inverse _ _ hmul

/-- Units on Spec C[z] are nonzero constants. -/
theorem frame_coordinate_constant (P : ProjectiveLineOverC) (i : Fin 2)
    (e : OverFrame (tangentSheaf P.structureMap) (chartOpen i)) :
    ∃ c : ℂ, c ≠ 0 ∧
      polynomialChartRingEquiv i
        (tangentActs P.structureMap (chartOpen i) (generator e) (coordinate i)) =
          Polynomial.C c := by
  have h := (frame_coordinate_unit P i e).map (polynomialChartRingEquiv i).toRingHom
  obtain ⟨c, hc, he⟩ := Polynomial.isUnit_iff.mp h
  exact ⟨c, hc.ne_zero, he.symm⟩

theorem generator_scaleFrame {E : ProjectiveLine.Modules} {U : ProjectiveLine.Opens}
    (e : OverFrame E U) (c : ℂˣ) :
    generator (scaleFrame e c) = ProjectiveLine.presheaf.map
      (homOfLE (show U ≤ ⊤ from le_top)).op
      (P1Endomorphisms.canonicalConstantRingHom c.val) • generator e := by
  rfl

/-- Normalize the derivative coefficient to one using the proved global
constant automorphism, without changing the local tangent sheaf. -/
theorem normalized_frame_exists (P : ProjectiveLineOverC) (i : Fin 2) :
    ∃ e : OverFrame (tangentSheaf P.structureMap) (chartOpen i),
      tangentActs P.structureMap (chartOpen i) (generator e) (coordinate i) = 1 := by
  let e : OverFrame (tangentSheaf P.structureMap) (chartOpen i) :=
    chartFrame (tangentLine P) i
  obtain ⟨c, hc, he⟩ := frame_coordinate_constant P i e
  let u : ℂˣ := (Units.mk0 c hc)⁻¹
  refine ⟨scaleFrame e u, ?_⟩
  rw [generator_scaleFrame, TangentActionProof.smul_field]
  apply (polynomialChartRingEquiv i).injective
  have hu : polynomialChartRingEquiv i
      (ProjectiveLine.presheaf.map (homOfLE (show chartOpen i ≤ ⊤ from le_top)).op
        (P1Endomorphisms.canonicalConstantRingHom u.val)) = Polynomial.C u.val :=
    polynomialChartRingEquiv_canonical_constant i u.val
  rw [map_mul, hu, he, ← map_mul, map_one]
  change Polynomial.C (c⁻¹ * c) = 1
  rw [inv_mul_cancel₀ hc, map_one]

def derivativeFrame (P : ProjectiveLineOverC) (i : Fin 2) :
    OverFrame (tangentSheaf P.structureMap) (chartOpen i) :=
  (normalized_frame_exists P i).choose

theorem derivativeFrame_coordinate (P : ProjectiveLineOverC) (i : Fin 2) :
    tangentActs P.structureMap (chartOpen i) (generator (derivativeFrame P i))
      (coordinate i) = 1 := (normalized_frame_exists P i).choose_spec

abbrev overlap : ProjectiveLine.Opens := chartOpen 0 ⊓ chartOpen 1
def z : RingSections ProjectiveLine overlap :=
  ProjectiveLine.presheaf.map (homOfLE inf_le_left).op (coordinate 0)
def w : RingSections ProjectiveLine overlap :=
  ProjectiveLine.presheaf.map (homOfLE inf_le_right).op (coordinate 1)

theorem z_laurent : overlapRingCoordinates z = LaurentPolynomial.T 1 := by
  change zeroRestrictionRingHom Polynomial.X = _
  rw [zeroRestrictionRingHom_eq_toLaurent, Polynomial.toLaurent_X]

theorem w_laurent : overlapRingCoordinates w = LaurentPolynomial.T (-1) := by
  change oneRestrictionRingHom Polynomial.X = _
  rw [oneRestrictionRingHom_eq_invert_toLaurent, RingHom.comp_apply,
    Polynomial.toLaurent_X]
  exact LaurentPolynomial.invert_T 1

theorem z_mul_w : z * w = 1 := by
  apply overlapRingCoordinates.injective
  rw [map_mul, z_laurent, w_laurent, ← LaurentPolynomial.T_add, map_one]
  norm_num

def frameZero (P : ProjectiveLineOverC) : OverFrame (tangentSheaf P.structureMap) overlap :=
  restrict (homOfLE inf_le_left) (derivativeFrame P 0)

def frameOne (P : ProjectiveLineOverC) : OverFrame (tangentSheaf P.structureMap) overlap :=
  restrict (homOfLE inf_le_right) (derivativeFrame P 1)

theorem frameZero_z (P : ProjectiveLineOverC) :
    tangentActs P.structureMap overlap (generator (frameZero P)) z = 1 := by
  rw [frameZero, ← generator_restrict, z, ← TangentActionProof.naturality,
    derivativeFrame_coordinate, map_one]

theorem frameOne_w (P : ProjectiveLineOverC) :
    tangentActs P.structureMap overlap (generator (frameOne P)) w = 1 := by
  rw [frameOne, ← generator_restrict, w, ← TangentActionProof.naturality,
    derivativeFrame_coordinate, map_one]

/-- The actual coordinate change w=z⁻¹ gives d/dw=-z² d/dz. -/
theorem frameOne_z (P : ProjectiveLineOverC) :
    tangentActs P.structureMap overlap (generator (frameOne P)) z = -(z ^ 2) := by
  exact derivation_reciprocal
    (tangentActs P.structureMap overlap (generator (frameOne P)))
    (tangentActs_leibniz P.structureMap overlap (generator (frameOne P)))
    z w z_mul_w (frameOne_w P)

theorem derivative_transition (P : ProjectiveLineOverC) :
    overlapRingCoordinates (transition (frameZero P) (frameOne P)) =
      -LaurentPolynomial.T 2 := by
  have h := congrArg (fun v => tangentActs P.structureMap overlap v z)
    (reconstruct (frameZero P) (generator (frameOne P)))
  rw [TangentActionProof.smul_field, frameZero_z, mul_one, frameOne_z] at h
  change transition (frameZero P) (frameOne P) = -(z ^ 2) at h
  rw [h, map_neg, map_pow, z_laurent, LaurentPolynomial.T_pow]
  norm_num

/-- Exact agreement of the two transition functions after the sign change. -/
theorem normalized_transition (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (d : ℤ) (hd : d = 2) :
    transition
      (restrict (homOfLE inf_le_left) (scaleFrame (derivativeFrame P 0) (-1)))
      (restrict (homOfLE inf_le_right) (derivativeFrame P 1)) =
    transition
      (restrict (homOfLE inf_le_left) (twistOverFrame P p d 0))
      (restrict (homOfLE inf_le_right) (twistOverFrame P p d 1)) := by
  let c : ℂˣ := -1
  apply overlapRingCoordinates.injective
  rw [restricted_scale_transition, map_mul, overlap_constant]
  change LaurentPolynomial.C (c.inv) *
    overlapRingCoordinates (transition (frameZero P) (frameOne P)) =
      (laurentTransitionUnit P p d).val
  rw [derivative_transition, laurentTransitionUnit_eq_T, hd]
  simp [c]

/-- Glue the normalized derivative frames to the project's actual O(2)
frames, including the sign from the reciprocal coordinate change. -/
def tangentTwistIsoAt (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P)
    (d : ℤ) (hd : d = 2) :
    tangentSheaf P.structureMap ≅ (projectiveTwist P p d).sheaf :=
  isoOfTransition (E := tangentSheaf P.structureMap)
    (F := (projectiveTwist P p d).sheaf)
    (chartOpen 0) (chartOpen 1) chartOpen_zero_sup_one
    (scaleFrame (derivativeFrame P 0) (-1)) (derivativeFrame P 1)
    (twistOverFrame P p d 0) (twistOverFrame P p d 1) (normalized_transition P p d hd)

def tangentTwistIso (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) :
    tangentSheaf P.structureMap ≅ (projectiveTwist P p 2).sheaf :=
  tangentTwistIsoAt P p 2 rfl

theorem tangentTwist (P : ProjectiveLineOverC) (p : ProjectiveLinePoint P) :
    Nonempty (tangentSheaf P.structureMap ≅ (projectiveTwist P p 2).sheaf) :=
  ⟨tangentTwistIso P p⟩

end LeBrunSalamon.P1TangentTranslation
