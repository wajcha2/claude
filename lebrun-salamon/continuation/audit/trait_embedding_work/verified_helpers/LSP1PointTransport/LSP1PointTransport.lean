import RecompileExtensionsPart01

/-! Actual projective-line point transport by explicit invertible matrices.
The scheme map, its inverse and its hyperplane-line comparison come from
the already proved quotient universal-property construction. No projective
transitivity theorem is admitted. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseSeven
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Skeleton

namespace LeBrunSalamon.P1PointTransport

private def firstPivot (v : Fin 2 → ℂ) (h : v 0 ≠ 0) :
    (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun a := ![v 0 * a 0, v 1 * a 0 + a 1]
  invFun b := ![b 0 / v 0, b 1 - v 1 * (b 0 / v 0)]
  left_inv a := by
    ext i
    fin_cases i <;> simp [h] <;> field_simp [h] <;> ring
  right_inv b := by
    ext i
    fin_cases i <;> simp [h] <;> field_simp [h] <;> ring
  map_add' a b := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c a := by
    ext i
    fin_cases i <;> simp <;> ring

private def secondPivot (v : Fin 2 → ℂ) (h0 : v 0 = 0) (h1 : v 1 ≠ 0) :
    (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun a := ![a 1, v 1 * a 0]
  invFun b := ![b 1 / v 1, b 0]
  left_inv a := by
    ext i
    fin_cases i <;> simp [h1] <;> field_simp [h1] <;> ring
  right_inv b := by
    ext i
    fin_cases i <;> simp [h1] <;> field_simp [h1] <;> ring
  map_add' a b := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c a := by
    ext i
    fin_cases i <;> simp <;> ring

theorem exists_matrix_firstColumn (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    ∃ T : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ), T ![1, 0] = v := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      ext i
      fin_cases i <;> simp [h0, h1]
    refine ⟨secondPivot v h0 h1, ?_⟩
    ext i
    fin_cases i <;> simp [secondPivot, h0]
  · refine ⟨firstPivot v h0, ?_⟩
    ext i
    fin_cases i <;> simp [firstPivot]

theorem exists_matrix_map (v w : Fin 2 → ℂ) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ T : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ), T v = w := by
  obtain ⟨A, hA⟩ := exists_matrix_firstColumn v hv
  obtain ⟨B, hB⟩ := exists_matrix_firstColumn w hw
  refine ⟨A.symm.trans B, ?_⟩
  change B (A.symm v) = w
  rw [← hA, A.symm_apply_apply, hB]

/-- An actual automorphism over C sends either prescribed rational point
to the other and carries the actual hyperplane line to itself. -/
theorem exists_iso (p q : ProjectiveLinePoint canonicalProjectiveLine) :
    ∃ e : ProjectiveLine ≅ ProjectiveLine,
      e.hom ≫ canonicalProjectiveLine.structureMap = canonicalProjectiveLine.structureMap ∧
      p.map ≫ e.hom = q.map ∧
      Nonempty (pullbackModule e.hom (projectiveCoordinates 1).hyperplane.sheaf ≅
        (projectiveCoordinates 1).hyperplane.sheaf) := by
  let P := projectiveCoordinates 1
  let x : PointsOver ComplexBase (𝟙 ComplexBase)
      (ComplexProjectiveSpace 1) (projectiveBaseMap 1) := ⟨p.map, p.overC⟩
  let y : PointsOver ComplexBase (𝟙 ComplexBase)
      (ComplexProjectiveSpace 1) (projectiveBaseMap 1) := ⟨q.map, q.overC⟩
  obtain ⟨v, hv⟩ := projectiveCoordinates_representatives P x
  obtain ⟨w, hw⟩ := projectiveCoordinates_representatives P y
  obtain ⟨T, hT⟩ := exists_matrix_map v w hv.1 hw.1
  obtain ⟨e, he, l, hl⟩ := AdjointComparisonProof.projectiveIso_of_linearEquiv P P T
  have ht := AdjointComparisonProof.represents_transport P P T e.hom he l hl x v hv
  rw [hT] at ht
  have hxy : (⟨x.val ≫ e.hom, by rw [Category.assoc, he, x.property]⟩ :
      PointsOver ComplexBase (𝟙 ComplexBase)
        (ComplexProjectiveSpace 1) (projectiveBaseMap 1)) = y :=
    (projectiveCoordinates_samePoint_iff P _ _ w w ht hw).mpr
      ⟨1, one_ne_zero, by simp⟩
  exact ⟨e, he, congrArg Subtype.val hxy, ⟨l⟩⟩

end LeBrunSalamon.P1PointTransport

end
