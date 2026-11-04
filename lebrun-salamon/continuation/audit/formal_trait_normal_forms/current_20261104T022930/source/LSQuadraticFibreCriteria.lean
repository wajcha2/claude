import LSQuadraticSchemeBaseChange
import LSQuadraticPolynomial
import LSPlaneQuadraticPublished
import LSFibreIsomorphism

/-! Apply the field discriminant criterion to the actual coefficientwise
base-changed quadratic of a given family isomorphism. Both scheme
comparisons and the nonzero-polynomial hypothesis are proved. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace LeBrunSalamon.QuadraticFibreCriteria

theorem smooth_of_family_iso
    {R K : Type} [CommRing R] [Field K] (φ : R →+* K)
    (q : PlaneQuadratic.Coefficients R)
    {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R))
    (e : X ≅ PlaneQuadratic.ZeroScheme R q)
    (he : e.hom ≫ PlaneQuadratic.projection R q = p)
    [Smooth (pullback.snd p (StandardProjectiveBaseChange.base φ))] :
    Smooth (PlaneQuadratic.projection K (fun i => φ (q i))) := by
  letI := FibreIsomorphism.smooth_target p (PlaneQuadratic.projection R q)
    e he (StandardProjectiveBaseChange.base φ)
  let u := QuadraticSchemeBaseChange.fibreIso φ q
  letI : IsIso u.hom := u.isIso_hom
  rw [← QuadraticSchemeBaseChange.fibreIso_projection φ q]
  infer_instance

theorem discriminant_ne_zero_of_family_iso
    {R K : Type} [CommRing R] [Field K] (φ : R →+* K)
    (q : PlaneQuadratic.Coefficients R) (hq : PlaneQuadratic.Primitive R q)
    {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R))
    (e : X ≅ PlaneQuadratic.ZeroScheme R q)
    (he : e.hom ≫ PlaneQuadratic.projection R q = p)
    [Smooth (pullback.snd p (StandardProjectiveBaseChange.base φ))] :
    PlaneQuadratic.discriminant K (fun i => φ (q i)) ≠ 0 :=
  (PublishedInputs.ConicQuadratic.smooth_iff_discriminant_ne_zero K _
    (QuadraticPolynomial.mapped_polynomial_ne_zero φ q hq)).mp
      (smooth_of_family_iso φ q p e he)

end LeBrunSalamon.QuadraticFibreCriteria
end
