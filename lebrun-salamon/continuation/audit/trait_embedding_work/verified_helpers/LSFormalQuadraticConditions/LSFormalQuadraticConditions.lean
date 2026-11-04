import LSStableMapFamily
import LSFormalTraitRing
import LSStandardProjectiveReduced
import LSReducedPushout
import LSResidueFibreGeometry
import LSFibreIsomorphism
import LSSmoothFibreComparison
import LSQuadraticPolynomial
import LSQuadraticFibreCriteria
import LSPlaneQuadraticPublished

/-! Supply the actual closed-fibre hypotheses for Tanaka's generic
quadratic theorem, on the original complex power-series trait. These
are explicit fibre, residue-field, reducedness and smoothness transports;
no family classification is admitted. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction
open LeBrunSalamon.Construction.StableMaps.FormalArcs

namespace LeBrunSalamon.FormalQuadraticConditions

abbrev R := PowerSeries ℂ

theorem smooth_residue_of_rational_fibre
    {X : Scheme.{0}} (pi : X ⟶ Trait) (q : PlaneQuadratic.Coefficients R)
    (e : X ≅ PlaneQuadratic.ZeroScheme R q)
    (he : e.hom ≫ PlaneQuadratic.projection R q = pi)
    (i : ProjectiveLine ≅ pullback pi closedPoint)
    (hi : i.hom ≫ pullback.snd pi closedPoint = Lines.P.structureMap) :
    Smooth (PlaneQuadratic.closedProjection R q) := by
  letI : IsLocalHom (PowerSeries.constantCoeff (R := ℂ)) :=
    ResidueFieldPresentation.constantCoeff_local ℂ
  letI : Smooth Lines.P.structureMap := StandardProjectiveSmooth.smooth ℂ 1
  letI : Smooth (pullback.snd pi closedPoint) := by
    rw [← SmoothFibreComparison.inverse_over Lines.P (pullback.snd pi closedPoint) i hi]
    infer_instance
  letI : Smooth (pullback.snd (PlaneQuadratic.projection R q)
      (ResidueFibreGeometry.quotientPoint (PowerSeries.constantCoeff (R := ℂ)))) :=
    FibreIsomorphism.smooth_target pi (PlaneQuadratic.projection R q) e he closedPoint
  exact ResidueFibreGeometry.smooth_residue (PlaneQuadratic.projection R q)
    PowerSeries.constantCoeff PowerSeries.constantCoeff_surj

theorem reduced_residue_of_pushout
    {X : Scheme.{0}} (pi : X ⟶ Trait) (c : PlaneQuadratic.Coefficients R)
    (e : X ≅ PlaneQuadratic.ZeroScheme R c)
    (he : e.hom ≫ PlaneQuadratic.projection R c = pi)
    (p q : ProjectiveLinePoint Lines.P)
    (i j : ProjectiveLine ⟶ pullback pi closedPoint)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (hpush : IsPushout p.map q.map i j) :
    IsReduced (PlaneQuadratic.ClosedFibre R c) := by
  letI : IsReduced ProjectiveLine := StandardProjectiveReduced.projectiveLine ℂ
  letI : IsReduced (pullback pi closedPoint) :=
    ReducedPushout.isReduced_of_isPushout p.map q.map i j hpush
  letI : IsReduced (pullback (PlaneQuadratic.projection R c)
      (ResidueFibreGeometry.quotientPoint (PowerSeries.constantCoeff (R := ℂ)))) :=
    FibreIsomorphism.reduced_target pi (PlaneQuadratic.projection R c) e he closedPoint
  letI : IsLocalHom (PowerSeries.constantCoeff (R := ℂ)) :=
    ResidueFieldPresentation.constantCoeff_local ℂ
  exact ResidueFibreGeometry.reduced_residue (PlaneQuadratic.projection R c)
    PowerSeries.constantCoeff PowerSeries.constantCoeff_surj

theorem notSmooth_residue_of_closed_fibre
    {X : Scheme.{0}} (pi : X ⟶ Trait) (q : PlaneQuadratic.Coefficients R)
    (e : X ≅ PlaneQuadratic.ZeroScheme R q)
    (he : e.hom ≫ PlaneQuadratic.projection R q = pi)
    (h : ¬ Smooth (pullback.snd pi closedPoint)) :
    ¬ Smooth (PlaneQuadratic.closedProjection R q) := by
  intro hs
  letI : Smooth (pullback.snd (PlaneQuadratic.projection R q)
      (ResidueFibreGeometry.residuePoint (R := R))) := hs
  letI : IsLocalHom (PowerSeries.constantCoeff (R := ℂ)) :=
    ResidueFieldPresentation.constantCoeff_local ℂ
  letI : Smooth (pullback.snd (PlaneQuadratic.projection R q) closedPoint) :=
    ResidueFibreGeometry.smooth_quotient (PlaneQuadratic.projection R q)
      PowerSeries.constantCoeff PowerSeries.constantCoeff_surj
  exact h (FibreIsomorphism.smooth_source pi (PlaneQuadratic.projection R q) e he closedPoint)

theorem notSmooth_of_split_zero_iso
    {Y : Scheme.{0}} (p : Y ⟶ ComplexBase)
    (e : Y ≅ PlaneQuadratic.ZeroScheme ℂ (PlaneQuadratic.split ℂ 0))
    (he : e.hom ≫ PlaneQuadratic.projection ℂ (PlaneQuadratic.split ℂ 0) = p) :
    ¬ Smooth p := by
  intro hp
  letI := hp
  have hi := FibreIsomorphism.inverse_over p
    (PlaneQuadratic.projection ℂ (PlaneQuadratic.split ℂ 0)) e he
  have hzero : PlaneQuadratic.split ℂ 0 ≠ 0 := by
    intro h
    have h5 := congrFun h 5
    norm_num [PlaneQuadratic.split] at h5
  have hs : Smooth (PlaneQuadratic.projection ℂ (PlaneQuadratic.split ℂ 0)) := by
    rw [← hi]
    infer_instance
  have hd := (PublishedInputs.ConicQuadratic.smooth_iff_discriminant_ne_zero ℂ
    (PlaneQuadratic.split ℂ 0) (QuadraticPolynomial.polynomial_ne_zero ℂ _ hzero)).mp hs
  exact hd (PlaneQuadratic.discriminant_split ℂ 0)

/-- The actual smooth generic fibre excludes the zero smoothing
coefficient in the diagonal normal form. No choice of uniformizer
or unit factor is discarded. -/
theorem diagonal_parameter_ne_zero
    {X : Scheme.{0}} (pi : X ⟶ Trait) (c : R)
    (e : X ≅ PlaneQuadratic.ZeroScheme R (PlaneQuadratic.diagonal R c))
    (he : e.hom ≫ PlaneQuadratic.projection R (PlaneQuadratic.diagonal R c) = pi)
    [Smooth (pullback.snd pi (Spec.map
      (CommRingCat.ofHom (algebraMap R (FractionRing R)))))] : c ≠ 0 := by
  intro hc
  subst c
  have hp : PlaneQuadratic.Primitive R (PlaneQuadratic.diagonal R 0) := by
    refine ⟨0, ?_⟩
    simp [PlaneQuadratic.diagonal]
  letI : Smooth (pullback.snd pi (StandardProjectiveBaseChange.base
      (algebraMap R (FractionRing R)))) :=
    ‹Smooth (pullback.snd pi (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))›
  have hd := QuadraticFibreCriteria.discriminant_ne_zero_of_family_iso
    (algebraMap R (FractionRing R)) (PlaneQuadratic.diagonal R 0) hp pi e he
  apply hd
  simp [PlaneQuadratic.discriminant, PlaneQuadratic.diagonal]

theorem reduced_normal_form
    (q : PlaneQuadratic.Coefficients R) (hq : PlaneQuadratic.Primitive R q)
    (hr : IsReduced (PlaneQuadratic.ClosedFibre R q))
    (hs : ¬ Smooth (PlaneQuadratic.closedProjection R q)) :
    ∃ (M : (Matrix (Fin 3) (Fin 3) R)ˣ) (c : R),
      PlaneQuadratic.transformed R q M = PlaneQuadratic.polynomial R (PlaneQuadratic.diagonal R c) ∧
      PowerSeries.constantCoeff c = 0 := by
  letI := FormalTraitRing.henselian ℂ
  letI := FormalTraitRing.residue_algebraicallyClosed ℂ
  obtain ⟨M, c, hM, hc⟩ := PublishedInputs.ConicQuadratic.reduced_normalForm R
    FormalTraitRing.complex_residue_two_ne_zero q hq hr
  exact ⟨M, c, hM, (FormalTraitRing.mem_maximal_iff_constantCoeff ℂ c).mp (hc.mpr hs)⟩

theorem smooth_normal_form
    (q : PlaneQuadratic.Coefficients R) (hq : PlaneQuadratic.Primitive R q)
    (hs : Smooth (PlaneQuadratic.closedProjection R q)) :
    ∃ M : (Matrix (Fin 3) (Fin 3) R)ˣ,
      PlaneQuadratic.transformed R q M = PlaneQuadratic.polynomial R (PlaneQuadratic.diagonal R 1) := by
  letI := FormalTraitRing.henselian ℂ
  letI := FormalTraitRing.residue_algebraicallyClosed ℂ
  exact PublishedInputs.ConicQuadratic.smooth_normalForm R
    FormalTraitRing.complex_residue_two_ne_zero q hq hs

end LeBrunSalamon.FormalQuadraticConditions
end
