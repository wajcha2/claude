import Mathlib

noncomputable section
set_option autoImplicit false
set_option profiler true
set_option stderrAsMessages false
set_option maxErrors 1

open CategoryTheory AlgebraicGeometry

namespace LeBrunSalamon.Next3i.SmoothRestrictionDensity

/-! Generic topology/scheme bridge only.  No Hom presentation, original052,
original057, or external published input occurs in these declarations. -/

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "DENSITY_STAGE ENTER_COMPOSITE"
  err.flush

theorem denseRange_of_smooth_composite {W X Y : Scheme}
    [Nonempty W] [PreirreducibleSpace Y]
    (j : W ⟶ X) (f : X ⟶ Y) [Smooth (j ≫ f)] :
    DenseRange f.base := by
  have hd : DenseRange (j ≫ f).base :=
    IsOpenMap.denseRange_of_isPreirreducibleSpace
      (j ≫ f).base (j ≫ f).isOpenMap
  exact DenseRange.of_comp (g := j.base) hd

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "DENSITY_STAGE EXIT_COMPOSITE"
  err.putStrLn "DENSITY_STAGE ENTER_POINT_NEIGHBORHOOD"
  err.flush

theorem denseRange_of_smooth_neighborhood {X Y : Scheme}
    [PreirreducibleSpace Y] (f : X ⟶ Y) (x : X)
    (h : ∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ f)) :
    DenseRange f.base := by
  obtain ⟨U, hx, hsmooth⟩ := h
  letI : Nonempty U.toScheme := ⟨⟨x, hx⟩⟩
  letI : Smooth (U.ι ≫ f) := hsmooth
  exact denseRange_of_smooth_composite U.ι f

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "DENSITY_STAGE EXIT_POINT_NEIGHBORHOOD"
  err.putStrLn "DENSITY_STAGE ENTER_POINT_MAP_NEIGHBORHOOD"
  err.flush

/-- This matches the open-neighborhood conclusion of the tangent-lift criterion. -/
theorem denseRange_of_smooth_pointMap_neighborhood {T X Y : Scheme}
    [Nonempty T] [PreirreducibleSpace Y] (f : X ⟶ Y) (x : T ⟶ X)
    (h : ∃ U : X.Opens, Set.range x ⊆ U ∧ Smooth (U.ι ≫ f)) :
    DenseRange f.base := by
  obtain ⟨U, hx, hsmooth⟩ := h
  let t : T := Classical.choice inferInstance
  exact denseRange_of_smooth_neighborhood f (x t)
    ⟨U, hx ⟨t, rfl⟩, hsmooth⟩

#eval show IO Unit from do
  let err ← IO.getStderr
  err.putStrLn "DENSITY_STAGE EXIT_POINT_MAP_NEIGHBORHOOD"
  err.putStrLn "DENSITY_COMPLETE"
  err.flush

#print axioms denseRange_of_smooth_composite
#print axioms denseRange_of_smooth_neighborhood
#print axioms denseRange_of_smooth_pointMap_neighborhood

end LeBrunSalamon.Next3i.SmoothRestrictionDensity
end
