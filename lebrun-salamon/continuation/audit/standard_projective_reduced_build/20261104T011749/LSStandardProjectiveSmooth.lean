import LSStandardTautological

/-! Standard affine charts of polynomial Proj, and their proved smooth
structure map.  The single generic published input is the standard
chart construction; smoothness is obtained from the actual chart maps. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace LeBrunSalamon.PublishedInputs.ProjectiveSpace

/-- Stacks, Lemma27.13.3 (01ND), with arbitrary coefficients by
Lemma27.16.10 (01O3), as in the relative construction immediately
following Definition27.13.2.  The
opens are the literal D_+(X_i), and the comparison commutes with the
literal coefficient morphisms.  This is only the generic standard-chart
construction, with no chosen curve or family in its statement. -/
theorem standardAffineCharts (R : Type) [CommRing R] (N : ℕ) :
    (⨆ i : Fin (N+1), StandardTautological.chart R N i) = ⊤ ∧
    ∀ i : Fin (N+1),
      ∃ e : (StandardTautological.chart R N i).toScheme ≅
          Spec (CommRingCat.of (MvPolynomial (Fin N) R)),
        e.hom ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin N) R)) =
          (StandardTautological.chart R N i).ι ≫ StandardTautological.toSpec R N := by
  sorry

end LeBrunSalamon.PublishedInputs.ProjectiveSpace

namespace LeBrunSalamon.StandardProjectiveSmooth

theorem affine (R : Type) [CommRing R] (N : ℕ) :
    SmoothOfRelativeDimension N
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin N) R))) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension N)]
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  change RingHom.IsStandardSmoothOfRelativeDimension N (algebraMap R (MvPolynomial (Fin N) R))
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap N).mpr inferInstance

theorem smooth_of_relative_dimension (R : Type) [CommRing R] (N : ℕ) :
    SmoothOfRelativeDimension N (StandardTautological.toSpec R N) := by
  obtain ⟨hcover, hcharts⟩ := PublishedInputs.ProjectiveSpace.standardAffineCharts R N
  apply IsZariskiLocalAtSource.of_iSup_eq_top (StandardTautological.chart R N) hcover
  intro i
  obtain ⟨e, he⟩ := hcharts i
  rw [← he]
  exact (MorphismProperty.cancel_left_of_respectsIso
    (@SmoothOfRelativeDimension N) e.hom _).mpr (affine R N)

theorem smooth (R : Type) [CommRing R] (N : ℕ) :
    Smooth (StandardTautological.toSpec R N) :=
  (smooth_of_relative_dimension R N).smooth

theorem flat (R : Type) [CommRing R] (N : ℕ) :
    Flat (StandardTautological.toSpec R N) := by
  letI := smooth R N
  infer_instance

theorem locallyOfFinitePresentation (R : Type) [CommRing R] (N : ℕ) :
    LocallyOfFinitePresentation (StandardTautological.toSpec R N) := by
  letI := smooth R N
  infer_instance

end LeBrunSalamon.StandardProjectiveSmooth
end
