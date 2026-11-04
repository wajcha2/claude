import LSPlaneQuadraticBaseChange
import LSConicGeneratingTuples

/-! The literal split quadratic is exactly the line-valued equation
x*y = a*z² under any normalized quotient tuple. No admission. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.Skeleton
open LeBrunSalamon.Refinement

namespace LeBrunSalamon.PlaneQuadraticEquation

theorem pull_sub {X Y : Scheme} (f : X ⟶ Y) {E : OModule Y}
    (s t : AlgebraicSection E) : pullSection f (s - t) = pullSection f s - pullSection f t := by
  simp only [pullSection, restrictSection, Functor.map_sub, Preadditive.comp_sub]

variable (R : Type) [CommRing R]

@[simp] theorem coefficient_zero : PlaneQuadratic.coefficient R 0 = 0 := by
  change (StandardTautological.toSpec R 2).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv 0) = 0
  rw [map_zero, map_zero]

@[simp] theorem coefficient_one : PlaneQuadratic.coefficient R 1 = 1 := by
  change (StandardTautological.toSpec R 2).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv 1) = 1
  rw [map_one, map_one]

@[simp] theorem coefficient_neg (a : R) :
    PlaneQuadratic.coefficient R (-a) = -PlaneQuadratic.coefficient R a := by
  change (StandardTautological.toSpec R 2).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv (-a)) =
      -(StandardTautological.toSpec R 2).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a)
  rw [map_neg, map_neg]

set_option maxHeartbeats 140000 in
theorem split_section (a : R) :
    PlaneQuadratic.sectionOf R (PlaneQuadratic.split R a) =
      tensorSection (StandardTautological.coordinate R 2 0)
        (StandardTautological.coordinate R 2 1) -
      ConicGeneratingTuples.scale (PlaneQuadratic.coefficient R a)
        (tensorSection (StandardTautological.coordinate R 2 2)
          (StandardTautological.coordinate R 2 2)) := by
  simp [PlaneQuadratic.sectionOf, PlaneQuadratic.split, Fin.sum_univ_succ,
    PlaneQuadratic.monomial, PlaneQuadratic.firstIndex, PlaneQuadratic.secondIndex,
    ConicGeneratingTuples.scale, sub_eq_add_neg]
  exact add_comm _ _

theorem pull_coefficient {T : Scheme} (f : T ⟶ PlaneQuadratic.Plane R)
    (s : T ⟶ Spec (CommRingCat.of R)) (hf : f ≫ StandardTautological.toSpec R 2 = s)
    (a : R) : f.appTop (PlaneQuadratic.coefficient R a) =
      s.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a) := by
  change ((StandardTautological.toSpec R 2).appTop ≫ f.appTop)
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a) = _
  rw [← Scheme.Hom.comp_appTop, hf]

theorem split_pullback {T : Scheme} (f : T ⟶ PlaneQuadratic.Plane R)
    (s : T ⟶ Spec (CommRingCat.of R)) (hf : f ≫ StandardTautological.toSpec R 2 = s)
    (L : LineBundle T) (b : Fin 3 → AlgebraicSection L.sheaf)
    (e : pullbackModule f (StandardTautological.line R 2).sheaf ≅ L.sheaf)
    (he : ∀ i, pullSection f (StandardTautological.coordinate R 2 i) ≫ e.hom = b i)
    (a : R) :
    pullSection f (PlaneQuadratic.sectionOf R (PlaneQuadratic.split R a)) ≫
      (PlaneQuadraticBaseChange.squarePullbackIso f
        (StandardTautological.line R 2).sheaf e).hom =
      tensorSection (b 0) (b 1) -
        ConicGeneratingTuples.scale (s.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a))
          (tensorSection (b 2) (b 2)) := by
  rw [split_section, pull_sub, Preadditive.sub_comp]
  rw [PlaneQuadraticBaseChange.squarePullbackIso_sections, he, he]
  change _ - pullSection f (sectionFromValue
    (PlaneQuadratic.coefficient R a • sectionValue (tensorSection _ _))) ≫ _ = _
  rw [LeBrunSalamon.Construction.Smoothing.StandardSourceProof.pullSection_scalar,
    LeBrunSalamon.Construction.Smoothing.StandardSourceProof.scalarSection_comp,
    PlaneQuadraticBaseChange.squarePullbackIso_sections, he, pull_coefficient R f s hf]
  rfl

/-- Vanishing of the actual quadratic section, with its scheme-theoretic
meaning, is equivalent to the displayed equation in the chosen line. -/
theorem split_zero_iff {T : Scheme} (f : T ⟶ PlaneQuadratic.Plane R)
    (s : T ⟶ Spec (CommRingCat.of R)) (hf : f ≫ StandardTautological.toSpec R 2 = s)
    (L : LineBundle T) (b : Fin 3 → AlgebraicSection L.sheaf)
    (e : pullbackModule f (StandardTautological.line R 2).sheaf ≅ L.sheaf)
    (he : ∀ i, pullSection f (StandardTautological.coordinate R 2 i) ≫ e.hom = b i)
    (a : R) :
    pullSection f (PlaneQuadratic.sectionOf R (PlaneQuadratic.split R a)) = 0 ↔
      tensorSection (b 0) (b 1) =
        ConicGeneratingTuples.scale (s.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a))
          (tensorSection (b 2) (b 2)) := by
  rw [← cancel_mono (PlaneQuadraticBaseChange.squarePullbackIso f
    (StandardTautological.line R 2).sheaf e).hom, zero_comp,
    split_pullback R f s hf L b e he a, sub_eq_zero]

end LeBrunSalamon.PlaneQuadraticEquation
end
