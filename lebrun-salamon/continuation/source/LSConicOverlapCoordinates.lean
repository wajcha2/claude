import LSConicOverlapAlgebra

/-! Actual regular-coordinate identities on the intersections of the conic
charts. The hypotheses identify the original scheme maps, so the conclusions
hold on arbitrary, possibly nonreduced, test schemes. No admission. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Construction.Smoothing
open LeBrunSalamon.Construction.Smoothing.CoordinateCharts
open LeBrunSalamon.Construction.Smoothing.SourceAffineCharts

namespace LeBrunSalamon.ConicOverlapCoordinates

abbrev value {T : Scheme} (a : T ⟶ Plane) (i : Fin 2) : RingSections T ⊤ :=
  a.appTop (planeFunction (MvPolynomial.X i))

theorem polynomialLine_X {T : Scheme} (a : T ⟶ Plane) (i : Fin 2) :
    (a ≫ polynomialLine (MvPolynomial.X i)).appTop parameterFunction = value a i := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, polynomialLine_parameter]

theorem node_left {T : Scheme} (F : StandardSource) (a b : T ⟶ Plane)
    (h : a ≫ modelMap F 0 = b ≫ modelMap F 1) :
    value a 0 * value b 1 = 1 ∧ value a 0 * value a 1 = value b 0 := by
  have hl := congrArg (fun f : T ⟶ F.source => f ≫ F.left) h
  have hp := congrArg (fun f : T ⟶ F.source => f ≫ F.parameter) h
  simp only [Category.assoc, (modelMap_spec F 0).2.1,
    (modelMap_spec F 1).2.1] at hl
  change (a ≫ polynomialLine (MvPolynomial.X 0)) ≫ (ratioPoint 0).val =
    (b ≫ polynomialLine (MvPolynomial.X 1)) ≫ (ratioPoint 1).val at hl
  have hinv := ConicOverlapAlgebra.reciprocal_of_equal_ratios
    (a ≫ polynomialLine (MvPolynomial.X 0))
    (b ≫ polynomialLine (MvPolynomial.X 1)) hl
  rw [polynomialLine_X, polynomialLine_X] at hinv
  refine ⟨hinv, ?_⟩
  simp only [Category.assoc, (modelMap_spec F 0).1,
    (modelMap_spec F 1).1] at hp
  have hv := congrArg (fun f : T ⟶ AffineLine => f.appTop parameterFunction) hp
  change (a ≫ polynomialLine (MvPolynomial.X 0 * MvPolynomial.X 1)).appTop
    parameterFunction = (b ≫ polynomialLine (MvPolynomial.X 0)).appTop parameterFunction at hv
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    polynomialLine_parameter, value, planeFunction, map_mul] using hv

theorem node_right {T : Scheme} (F : StandardSource) (a b : T ⟶ Plane)
    (h : a ≫ modelMap F 0 = b ≫ modelMap F 2) :
    value a 1 * value b 1 = 1 ∧ value a 0 * value a 1 = value b 0 := by
  have hr := congrArg (fun f : T ⟶ F.source => f ≫ F.right) h
  have hp := congrArg (fun f : T ⟶ F.source => f ≫ F.parameter) h
  simp only [Category.assoc, (modelMap_spec F 0).2.2,
    (modelMap_spec F 2).2.2] at hr
  change (a ≫ polynomialLine (MvPolynomial.X 1)) ≫ (ratioPoint 0).val =
    (b ≫ polynomialLine (MvPolynomial.X 1)) ≫ (ratioPoint 1).val at hr
  have hinv := ConicOverlapAlgebra.reciprocal_of_equal_ratios
    (a ≫ polynomialLine (MvPolynomial.X 1))
    (b ≫ polynomialLine (MvPolynomial.X 1)) hr
  rw [polynomialLine_X, polynomialLine_X] at hinv
  refine ⟨hinv, ?_⟩
  simp only [Category.assoc, (modelMap_spec F 0).1,
    (modelMap_spec F 2).1] at hp
  have hv := congrArg (fun f : T ⟶ AffineLine => f.appTop parameterFunction) hp
  change (a ≫ polynomialLine (MvPolynomial.X 0 * MvPolynomial.X 1)).appTop
    parameterFunction = (b ≫ polynomialLine (MvPolynomial.X 0)).appTop parameterFunction at hv
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    polynomialLine_parameter, value, planeFunction, map_mul] using hv

/-- The affine chart really is the same open embedding in both directions. -/
@[reassoc] theorem chartToModel_modelMap (F : StandardSource) (k : Fin 3) :
    chartToModel F k ≫ modelMap F k = (chartOpen F (leftIndex k) (rightIndex k)).ι := by
  rw [← modelToChart_inclusion, ← Category.assoc]
  change ((chartIso F k).hom ≫ (chartIso F k).inv) ≫ _ = _
  rw [Iso.hom_inv_id, Category.id_comp]

/-- The overlap of the two outer charts is contained in the node chart.
This reduces all three pairwise compatibilities to the two computed ones. -/
theorem outer_overlap_factor {T : Scheme} (F : StandardSource) (a b : T ⟶ Plane)
    (h : a ≫ modelMap F 1 = b ≫ modelMap F 2) :
    ∃ c : T ⟶ Plane, c ≫ modelMap F 0 = a ≫ modelMap F 1 := by
  have hrange : Set.range (a ≫ modelMap F 1) ⊆
      Set.range (chartOpen F 0 0).ι := by
    rw [Scheme.Opens.range_ι]
    rintro x ⟨z, rfl⟩
    change F.left ((modelMap F 1) (a z)) ∈ ratioOpen 0 ∧
      F.right ((modelMap F 1) (a z)) ∈ ratioOpen 0
    constructor
    · have hb := modelMap_range F 2 ⟨b z, rfl⟩
      have he := congrArg (fun f : T ⟶ F.source => f z) h
      change (modelMap F 1) (a z) = (modelMap F 2) (b z) at he
      rw [he]
      exact hb.1
    · exact (modelMap_range F 1 ⟨a z, rfl⟩).2
  let z := IsOpenImmersion.lift (chartOpen F 0 0).ι (a ≫ modelMap F 1) hrange
  have hz : z ≫ (chartOpen F 0 0).ι = a ≫ modelMap F 1 :=
    IsOpenImmersion.lift_fac _ _ _
  refine ⟨z ≫ chartToModel F 0, ?_⟩
  rw [Category.assoc, chartToModel_modelMap]
  exact hz

end LeBrunSalamon.ConicOverlapCoordinates
end
