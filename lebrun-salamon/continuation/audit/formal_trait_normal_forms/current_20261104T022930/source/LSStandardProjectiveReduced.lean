import LSStandardProjectiveSmooth

/-!
Reducedness of the actual polynomial Proj used by StandardTautological.
This is a proof from the existing standard affine charts, reducedness of
polynomial rings, and Mathlib's open-cover criterion.  It introduces no
new published input.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace LeBrunSalamon.StandardProjectiveReduced

/-- Every standard affine chart is reduced over a reduced coefficient ring. -/
theorem chart (R : Type) [CommRing R] [_root_.IsReduced R] (N : ℕ)
    (i : Fin (N + 1)) :
    AlgebraicGeometry.IsReduced (StandardTautological.chart R N i).toScheme := by
  obtain ⟨e, _⟩ := (PublishedInputs.ProjectiveSpace.standardAffineCharts R N).2 i
  exact isReduced_of_isOpenImmersion e.hom

/-- Polynomial projective space over any reduced ring is reduced. -/
theorem space (R : Type) [CommRing R] [_root_.IsReduced R] (N : ℕ) :
    AlgebraicGeometry.IsReduced (StandardTautological.space R N) := by
  let cover := (StandardTautological.space R N).openCoverOfIsOpenCover
    (StandardTautological.chart R N)
    (PublishedInputs.ProjectiveSpace.standardAffineCharts R N).1
  letI (i : cover.I₀) : AlgebraicGeometry.IsReduced (cover.X i) := chart R N i
  exact AlgebraicGeometry.IsReduced.of_openCover _ cover

/-- In particular, the literal normalized projective line over a field is reduced. -/
theorem projectiveLine (K : Type) [Field K] :
    AlgebraicGeometry.IsReduced (StandardTautological.space K 1) :=
  space K 1

end LeBrunSalamon.StandardProjectiveReduced
end
