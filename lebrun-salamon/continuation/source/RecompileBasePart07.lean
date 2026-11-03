import RecompileBasePart06

noncomputable section

set_option autoImplicit false
open Bundle
open scoped Bundle ContDiff ENNReal
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 100] LieRing.ofAssociativeRing
open CategoryTheory
open AlgebraicGeometry
open CategoryTheory.Limits


/-! Normalized affine kernel frames, actual overlaps, and gluing of module isomorphisms. -/
section PointIdealTransitionAndGluing

/- BEGIN checked component ideal_frames.lean -/

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped LaurentPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LeBrunSalamon.P1Ideal

/-- The point-ideal generator on the first polynomial chart for the point [1:a]. -/
def finiteGeneratorZero (a : ℂ) : Polynomial ℂ := Polynomial.X - Polynomial.C a

/-- The normalized generator on the second chart, including the disjoint-chart case a=0. -/
def finiteGeneratorOne (a : ℂ) : Polynomial ℂ :=
  1 - Polynomial.C a * Polynomial.X

theorem finiteGeneratorZero_ne_zero (a : ℂ) : finiteGeneratorZero a ≠ 0 :=
  Polynomial.X_sub_C_ne_zero a

@[simp]
theorem finiteGeneratorOne_coeff_zero (a : ℂ) :
    (finiteGeneratorOne a).coeff 0 = 1 := by
  simp [finiteGeneratorOne]

theorem finiteGeneratorOne_ne_zero (a : ℂ) : finiteGeneratorOne a ≠ 0 := by
  intro h
  have hc := congrArg (fun p : Polynomial ℂ => p.coeff 0) h
  simpa using hc

@[simp]
theorem finiteGeneratorOne_zero : finiteGeneratorOne 0 = 1 := by
  simp [finiteGeneratorOne]

/-- On a containing second chart the chosen frame is a unit multiple of the evaluation frame. -/
theorem finiteGeneratorOne_eq (a : ℂ) (ha : a ≠ 0) :
    finiteGeneratorOne a =
      Polynomial.C (-a) * (Polynomial.X - Polynomial.C a⁻¹) := by
  simp only [finiteGeneratorOne, mul_sub, ← Polynomial.C_mul, neg_mul,
    mul_inv_cancel₀ ha, Polynomial.C_neg, map_one]
  ring

theorem finiteGeneratorZero_span (a : ℂ) :
    Ideal.span {finiteGeneratorZero a} = RingHom.ker (Polynomial.evalRingHom a) :=
  (Polynomial.ker_evalRingHom a).symm

theorem finiteGeneratorOne_span (a : ℂ) (ha : a ≠ 0) :
    Ideal.span {finiteGeneratorOne a} =
      RingHom.ker (Polynomial.evalRingHom a⁻¹) := by
  rw [finiteGeneratorOne_eq a ha,
    Ideal.span_singleton_mul_left_unit
      ((isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr ha)).map Polynomial.C)]
  exact (Polynomial.ker_evalRingHom a⁻¹).symm

@[simp]
theorem finiteGeneratorOne_eval_inv (a : ℂ) (ha : a ≠ 0) :
    Polynomial.eval a⁻¹ (finiteGeneratorOne a) = 0 := by
  simp [finiteGeneratorOne, ha]

/-- The normalized generators satisfy the transition equation in the actual Laurent coordinates. -/
theorem finiteGenerators_laurent_transition (a : ℂ) :
    LaurentPolynomial.invert (finiteGeneratorOne a).toLaurent =
      LaurentPolynomial.T (-1) * (finiteGeneratorZero a).toLaurent := by
  simp only [finiteGeneratorOne, finiteGeneratorZero, map_sub, map_one, map_mul,
    Polynomial.toLaurent_C, Polynomial.toLaurent_X, LaurentPolynomial.invert_C,
    LaurentPolynomial.invert_T]
  rw [mul_sub, ← LaurentPolynomial.T_add]
  simp only [neg_add_cancel, LaurentPolynomial.T_zero]
  ring

/-- At infinity, the ideal frames 1 and s obey the same transition. -/
theorem infinityGenerators_laurent_transition :
    LaurentPolynomial.invert (Polynomial.X : Polynomial ℂ).toLaurent =
      LaurentPolynomial.T (-1) * (1 : Polynomial ℂ).toLaurent := by
  simp

/-- The finite-point transition expressed in the actual homogeneous-localization overlap ring. -/
theorem finiteGenerators_overlap_transition (a : ℂ) :
    P1Charts.chartOneToOverlap
        ((P1Charts.chartRingEquiv 1).symm (finiteGeneratorOne a)) =
      P1Charts.chartOneToOverlap (P1Charts.ratio 1 0) *
        P1Charts.chartZeroToOverlap
          ((P1Charts.chartRingEquiv 0).symm (finiteGeneratorZero a)) := by
  apply P1Charts.overlapRingEquiv.injective
  rw [map_mul, P1Charts.overlapRingEquiv_chartOne,
    P1Charts.overlapRingEquiv_ratioOne, P1Charts.overlapRingEquiv_chartZero]
  change LaurentPolynomial.invert
      (P1Charts.chartRingEquiv 1 ((P1Charts.chartRingEquiv 1).symm _)).toLaurent =
    LaurentPolynomial.T (-1) *
      (P1Charts.chartRingEquiv 0 ((P1Charts.chartRingEquiv 0).symm _)).toLaurent
  simp only [RingEquiv.apply_symm_apply]
  exact finiteGenerators_laurent_transition a

/-- The same homogeneous-localization transition for the point at infinity. -/
theorem infinityGenerators_overlap_transition :
    P1Charts.chartOneToOverlap
        ((P1Charts.chartRingEquiv 1).symm (Polynomial.X : Polynomial ℂ)) =
      P1Charts.chartOneToOverlap (P1Charts.ratio 1 0) *
        P1Charts.chartZeroToOverlap
          ((P1Charts.chartRingEquiv 0).symm (1 : Polynomial ℂ)) := by
  rw [P1Charts.chartRingEquiv_symm_X 1 0 (by decide)]
  simp

/-- The common transition factor is invertible on the actual overlap. -/
theorem idealTransition_isUnit :
    IsUnit (P1Charts.chartOneToOverlap (P1Charts.ratio 1 0)) := by
  refine ⟨⟨P1Charts.chartOneToOverlap (P1Charts.ratio 1 0),
    P1Charts.chartZeroToOverlap (P1Charts.ratio 0 1), ?_, ?_⟩, rfl⟩
  · simpa only [mul_comm] using P1Charts.overlap_coordinates_inverse
  · exact P1Charts.overlap_coordinates_inverse

end LeBrunSalamon.P1Ideal
/- END checked component ideal_frames.lean -/

/- BEGIN checked component ideal_point_coordinates.lean -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped LaurentPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LeBrunSalamon.P1Charts

/-- The two embeddings of the actual overlap agree as maps to Proj. -/
theorem overlapInclusions_comp :
    Spec.map (CommRingCat.ofHom chartZeroToOverlap) ≫ chartInclusion 0 =
      Spec.map (CommRingCat.ofHom chartOneToOverlap) ≫ chartInclusion 1 := by
  change Spec.map (CommRingCat.ofHom
      (HomogeneousLocalization.awayMap grading (variable_degree 1) rfl)) ≫
        Proj.awayι grading (MvPolynomial.X 0) (variable_degree 0) (by decide) =
    Spec.map (CommRingCat.ofHom
      (HomogeneousLocalization.awayMap grading (variable_degree 0) (mul_comm _ _))) ≫
        Proj.awayι grading (MvPolynomial.X 1) (variable_degree 1) (by decide)
  rw [Proj.SpecMap_awayMap_awayι, Proj.SpecMap_awayMap_awayι]

/-- Evaluation of the actual overlap at a nonzero first-chart coordinate. -/
def overlapEval (a : ℂ) (ha : a ≠ 0) : OverlapRing →+* ℂ :=
  (LaurentPolynomial.eval₂ (RingHom.id ℂ) (Units.mk0 a ha)).comp overlapRingEquiv.toRingHom

theorem overlapEval_chartZero (a : ℂ) (ha : a ≠ 0) :
    (overlapEval a ha).comp chartZeroToOverlap = pointEval 0 a := by
  ext x
  simp [overlapEval, pointEval, overlapRingEquiv_chartZero,
    LaurentPolynomial.eval₂_toLaurent]

theorem laurentEval_invert_toLaurent (a : ℂ) (ha : a ≠ 0) (p : Polynomial ℂ) :
    LaurentPolynomial.eval₂ (RingHom.id ℂ) (Units.mk0 a ha)
      (LaurentPolynomial.invert p.toLaurent) = Polynomial.eval a⁻¹ p := by
  have h :
      (LaurentPolynomial.eval₂ (RingHom.id ℂ) (Units.mk0 a ha)).comp
        (LaurentPolynomial.invert.toRingHom.comp
          (Polynomial.toLaurent : Polynomial ℂ →+* ℂ[T;T⁻¹])) =
        Polynomial.evalRingHom a⁻¹ := by
    apply Polynomial.ringHom_ext
    · intro c
      simp [LaurentPolynomial.eval₂_C]
    · simp [LaurentPolynomial.eval₂_T]
  exact congrArg (fun f : Polynomial ℂ →+* ℂ => f p) h

theorem overlapEval_chartOne (a : ℂ) (ha : a ≠ 0) :
    (overlapEval a ha).comp chartOneToOverlap = pointEval 1 a⁻¹ := by
  ext x
  change LaurentPolynomial.eval₂ (RingHom.id ℂ) (Units.mk0 a ha)
      (overlapRingEquiv (chartOneToOverlap x)) =
    Polynomial.eval a⁻¹ (chartToPolynomial 1 x)
  rw [overlapRingEquiv_chartOne, laurentEval_invert_toLaurent]

/-- The standard inverse-coordinate relation holds for actual scheme-valued points. -/
theorem pointMap_zero_eq_one_inv (a : ℂ) (ha : a ≠ 0) :
    pointMap 0 a = pointMap 1 a⁻¹ := by
  calc
    pointMap 0 a =
        Spec.map (CommRingCat.ofHom (overlapEval a ha)) ≫
          (Spec.map (CommRingCat.ofHom chartZeroToOverlap) ≫ chartInclusion 0) := by
      rw [← Category.assoc, ← Spec.map_comp]
      change Spec.map (CommRingCat.ofHom (pointEval 0 a)) ≫ chartInclusion 0 =
        Spec.map (CommRingCat.ofHom ((overlapEval a ha).comp chartZeroToOverlap)) ≫
          chartInclusion 0
      rw [overlapEval_chartZero]
    _ = Spec.map (CommRingCat.ofHom (overlapEval a ha)) ≫
          (Spec.map (CommRingCat.ofHom chartOneToOverlap) ≫ chartInclusion 1) := by
      rw [overlapInclusions_comp]
    _ = pointMap 1 a⁻¹ := by
      rw [← Category.assoc, ← Spec.map_comp]
      change Spec.map (CommRingCat.ofHom ((overlapEval a ha).comp chartOneToOverlap)) ≫
          chartInclusion 1 =
        Spec.map (CommRingCat.ofHom (pointEval 1 a⁻¹)) ≫ chartInclusion 1
      rw [overlapEval_chartOne]

theorem pointMap_one_eq_zero_inv (a : ℂ) (ha : a ≠ 0) :
    pointMap 1 a = pointMap 0 a⁻¹ := by
  simpa only [inv_inv] using (pointMap_zero_eq_one_inv a⁻¹ (inv_ne_zero ha)).symm

/-- Every point over the canonical complex base is a finite coordinate point or infinity. -/
theorem canonicalPoint_finite_or_infinity
    (p : Spec (CommRingCat.of ℂ) ⟶ lineScheme)
    (hp : p ≫ canonicalBaseMap = 𝟙 (Spec (CommRingCat.of ℂ))) :
    (∃ a : ℂ, p = pointMap 0 a) ∨ p = pointMap 1 0 := by
  obtain ⟨i, a, rfl⟩ := canonicalPoint_is_coordinate p hp
  fin_cases i
  · exact Or.inl ⟨a, rfl⟩
  · by_cases ha : a = 0
    · exact Or.inr (by rw [ha]; rfl)
    · exact Or.inl ⟨a⁻¹, pointMap_one_eq_zero_inv a ha⟩


end LeBrunSalamon.P1Charts
/- END checked component ideal_point_coordinates.lean -/

/- BEGIN checked component ideal_kernel_normalization.lean -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentyEight

namespace LeBrunSalamon.P1Ideal

@[reassoc]
theorem affineKernelIso_hom_ι {R : CommRingCat} {M N : (Spec R).Modules}
    (f : M ⟶ N) [IsIso M.fromTildeΓ] [IsIso N.fromTildeΓ] :
    (affineKernelIso f).hom ≫ kernel.ι f =
      (tilde.functor R).map (kernel.ι ((moduleSpecΓFunctor (R := R)).map f)) ≫
        M.fromTildeΓ := by
  simp [affineKernelIso, Category.assoc]

@[reassoc]
theorem affineKernelLinearIso_hom_ι {R : CommRingCat} {M N : (Spec R).Modules}
    (f : M ⟶ N) [IsIso M.fromTildeΓ] [IsIso N.fromTildeΓ] :
    (affineKernelLinearIso f).hom ≫ kernel.ι f =
      (tilde.functor R).map
        (ModuleCat.ofHom ((moduleSpecΓFunctor (R := R)).map f).hom.ker.subtype) ≫
          M.fromTildeΓ := by
  simp only [affineKernelLinearIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Category.assoc, affineKernelIso_hom_ι]
  rw [← Category.assoc, ← Functor.map_comp, ModuleCat.kernelIsoKer_inv_kernel_ι]

@[simp]
theorem affineStructureKernelLinearIso_apply {R S : CommRingCat} (φ : R ⟶ S)
    (x : RingHom.ker φ.hom) :
    (affineStructureKernelLinearIso φ x).val =
      (tilde.isoTop (ModuleCat.of R R)).hom x.val := rfl

@[reassoc]
theorem affineStructureKernelIso_hom_ι {R S : CommRingCat} (φ : R ⟶ S) :
    (affineStructureKernelIso φ).hom ≫ kernel.ι (structurePushforwardMap (Spec.map φ)) =
      (tilde.functor R).map (ModuleCat.ofHom (RingHom.ker φ.hom).subtype) := by
  simp only [affineStructureKernelIso, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc, affineKernelLinearIso_hom_ι]
  rw [← Category.assoc, ← Functor.map_comp]
  have h : (affineStructureKernelLinearIso φ).toModuleIso.hom ≫
      ModuleCat.ofHom ((moduleSpecΓFunctor (R := R)).map
        (structurePushforwardMap (Spec.map φ))).hom.ker.subtype =
      ModuleCat.ofHom (RingHom.ker φ.hom).subtype ≫
        (tilde.isoTop (ModuleCat.of R R)).hom := by
    ext x
    rfl
  rw [h, Functor.map_comp, Category.assoc]
  have ht := (tilde.adjunction (R := R)).left_triangle_components (ModuleCat.of R R)
  change (tilde.functor R).map (tilde.isoTop (ModuleCat.of R R)).hom ≫
      (structureModule (Spec R)).fromTildeΓ = 𝟙 _ at ht
  rw [ht, Category.comp_id]

@[simp]
theorem polynomialEvalKernelEquiv_apply (a : ℂ) (f : Polynomial ℂ) :
    (polynomialEvalKernelEquiv a f).val = f * (Polynomial.X - Polynomial.C a) := rfl

/-- The affine ideal basis is normalized by the actual kernel inclusion. -/
@[reassoc]
theorem affinePointIdealTrivialization_inv_ι (a : ℂ) :
    (affinePointIdealTrivialization a).inv ≫
        kernel.ι (structurePushforwardMap
          (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)))) =
      (tilde.functor (CommRingCat.of (Polynomial ℂ))).map
        (ModuleCat.ofHom (LinearMap.mulRight (Polynomial ℂ)
          (Polynomial.X - Polynomial.C a))) := by
  simp only [affinePointIdealTrivialization, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, tildeSelf, Iso.refl_inv,
    Category.assoc, affineStructureKernelIso_hom_ι]
  rw [← Functor.map_comp]
  congr 1

/-- Restriction to a containing chart preserves the actual ideal inclusion. -/
@[reassoc]
theorem structureKernel_restrict_comp_hom_ι {S U X : Scheme} (p : S ⟶ U)
    (j : U ⟶ X) [IsOpenImmersion j] :
    (structureKernel_restrict_comp p j).hom ≫ kernel.ι (structurePushforwardMap p) =
      (Scheme.Modules.restrictFunctor j).map
        (kernel.ι (structurePushforwardMap (p ≫ j))) ≫
          (Scheme.Modules.restrictUnitIso j).hom := by
  simp [structureKernel_restrict_comp, Category.assoc]

/-- Restriction to a disjoint chart identifies the ideal inclusion with the unit. -/
@[reassoc]
theorem structureKernel_restrict_disjoint_hom {S X U : Scheme} (p : S ⟶ X)
    (j : U ⟶ X) [IsOpenImmersion j] (h : p ⁻¹ᵁ j.opensRange = ⊥) :
    (structureKernel_restrict_disjoint p j h).hom =
      (Scheme.Modules.restrictFunctor j).map (kernel.ι (structurePushforwardMap p)) ≫
        (Scheme.Modules.restrictUnitIso j).hom := by
  simp [structureKernel_restrict_disjoint]


end LeBrunSalamon.P1Ideal
/- END checked component ideal_kernel_normalization.lean -/

/- BEGIN checked component ideal_affine_frames.lean -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentyEight

namespace LeBrunSalamon.P1Ideal

/-- A specified nonzero generator of an affine ring kernel gives a normalized
frame of the actual structure-sheaf kernel. -/
def affineStructureKernelGeneratorIso {R S : CommRingCat} [IsDomain R]
    (φ : R ⟶ S) (g : R) (hg : g ≠ 0)
    (hker : RingHom.ker φ.hom = Ideal.span {g}) :
    structureModule (Spec R) ≅ kernel (structurePushforwardMap (Spec.map φ)) :=
  tildeSelf.symm ≪≫
    (tilde.functor R).mapIso
      ((LinearEquiv.toSpanNonzeroSingleton R R g hg).trans
        (LinearEquiv.ofEq _ _ hker.symm)).toModuleIso ≪≫
      affineStructureKernelIso φ

@[reassoc]
theorem affineStructureKernelGeneratorIso_hom_ι {R S : CommRingCat} [IsDomain R]
    (φ : R ⟶ S) (g : R) (hg : g ≠ 0)
    (hker : RingHom.ker φ.hom = Ideal.span {g}) :
    (affineStructureKernelGeneratorIso φ g hg hker).hom ≫
        kernel.ι (structurePushforwardMap (Spec.map φ)) =
      (tilde.functor R).map (ModuleCat.ofHom (LinearMap.mulRight R g)) := by
  simp only [affineStructureKernelGeneratorIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, tildeSelf, Iso.refl_inv, Category.id_comp,
    Category.assoc, affineStructureKernelIso_hom_ι]
  rw [← Functor.map_comp]
  congr 1

/-- The normalized first-chart frame of the point [1:a]. -/
def finitePointFirstFrame (a : ℂ) :
    structureModule (Spec (CommRingCat.of (Polynomial ℂ))) ≅
      kernel (structurePushforwardMap
        (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)))) :=
  affineStructureKernelGeneratorIso
    (CommRingCat.ofHom (Polynomial.evalRingHom a))
    (finiteGeneratorZero a) (finiteGeneratorZero_ne_zero a) (finiteGeneratorZero_span a).symm

/-- For a nonzero finite point, the second-chart frame is normalized as 1-a*s. -/
def finitePointSecondFrame (a : ℂ) (ha : a ≠ 0) :
    structureModule (Spec (CommRingCat.of (Polynomial ℂ))) ≅
      kernel (structurePushforwardMap
        (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a⁻¹)))) :=
  affineStructureKernelGeneratorIso
    (CommRingCat.ofHom (Polynomial.evalRingHom a⁻¹))
    (finiteGeneratorOne a) (finiteGeneratorOne_ne_zero a) (finiteGeneratorOne_span a ha).symm

@[reassoc]
theorem finitePointFirstFrame_hom_ι (a : ℂ) :
    (finitePointFirstFrame a).hom ≫ kernel.ι (structurePushforwardMap
        (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)))) =
      (tilde.functor (CommRingCat.of (Polynomial ℂ))).map
        (ModuleCat.ofHom (LinearMap.mulRight (Polynomial ℂ) (finiteGeneratorZero a))) :=
  affineStructureKernelGeneratorIso_hom_ι _ _ _ _

@[reassoc]
theorem finitePointSecondFrame_hom_ι (a : ℂ) (ha : a ≠ 0) :
    (finitePointSecondFrame a ha).hom ≫ kernel.ι (structurePushforwardMap
        (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a⁻¹)))) =
      (tilde.functor (CommRingCat.of (Polynomial ℂ))).map
        (ModuleCat.ofHom (LinearMap.mulRight (Polynomial ℂ) (finiteGeneratorOne a))) :=
  affineStructureKernelGeneratorIso_hom_ι _ _ _ _

/-- Changing the first-chart presentation preserves the previously chosen normalization. -/
theorem finitePointFirstFrame_eq (a : ℂ) :
    finitePointFirstFrame a = (affinePointIdealTrivialization a).symm := by
  apply Iso.ext
  apply (cancel_mono (kernel.ι (structurePushforwardMap
    (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)))))).mp
  rw [finitePointFirstFrame_hom_ι]
  exact (affinePointIdealTrivialization_inv_ι a).symm


end LeBrunSalamon.P1Ideal
/- END checked component ideal_affine_frames.lean -/

/- BEGIN checked component ideal_chart_core.lean -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.P1Charts
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LeBrunSalamon.P1Ideal

/-- Equality of structure morphisms transports their actual kernels. -/
def structureKernelIsoOfEq {S X : Scheme} {p q : S ⟶ X} (h : p = q) :
    kernel (structurePushforwardMap p) ≅ kernel (structurePushforwardMap q) :=
  eqToIso (congrArg (fun f : S ⟶ X => kernel (structurePushforwardMap f)) h)

@[reassoc (attr := simp)]
theorem structureKernelIsoOfEq_hom_ι {S X : Scheme} {p q : S ⟶ X} (h : p = q) :
    (structureKernelIsoOfEq h).hom ≫ kernel.ι (structurePushforwardMap q) =
      kernel.ι (structurePushforwardMap p) := by
  subst q
  simp [structureKernelIsoOfEq]

/-- The affine restriction comparison with an explicitly supplied factorization. -/
def structureKernel_restrict_comp_of_eq {S U X : Scheme}
    (p : S ⟶ X) (q : S ⟶ U) (j : U ⟶ X) [IsOpenImmersion j] (h : q ≫ j = p) :
    (kernel (structurePushforwardMap p)).restrict j ≅ kernel (structurePushforwardMap q) :=
  (Scheme.Modules.restrictFunctor j).mapIso (structureKernelIsoOfEq h.symm) ≪≫
    structureKernel_restrict_comp q j

@[reassoc]
theorem structureKernel_restrict_comp_of_eq_hom_ι {S U X : Scheme}
    (p : S ⟶ X) (q : S ⟶ U) (j : U ⟶ X) [IsOpenImmersion j] (h : q ≫ j = p) :
    (structureKernel_restrict_comp_of_eq p q j h).hom ≫
        kernel.ι (structurePushforwardMap q) =
      (Scheme.Modules.restrictFunctor j).map (kernel.ι (structurePushforwardMap p)) ≫
        (Scheme.Modules.restrictUnitIso j).hom := by
  simp only [structureKernel_restrict_comp_of_eq, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc, structureKernel_restrict_comp_hom_ι]
  rw [← Category.assoc, ← Functor.map_comp, structureKernelIsoOfEq_hom_ι]

/-- Transfer a specified affine kernel frame to the restriction of the global point ideal. -/
def structureKernelFrameOfFactor {S U X : Scheme}
    (p : S ⟶ X) (q : S ⟶ U) (j : U ⟶ X) [IsOpenImmersion j] (h : q ≫ j = p)
    (e : structureModule U ≅ kernel (structurePushforwardMap q)) :
    structureModule U ≅ (kernel (structurePushforwardMap p)).restrict j :=
  e ≪≫ (structureKernel_restrict_comp_of_eq p q j h).symm

/-- The transferred frame retains its actual kernel-inclusion equation. -/
@[reassoc]
theorem structureKernelFrameOfFactor_hom_inclusion {S U X : Scheme}
    (p : S ⟶ X) (q : S ⟶ U) (j : U ⟶ X) [IsOpenImmersion j] (h : q ≫ j = p)
    (e : structureModule U ≅ kernel (structurePushforwardMap q)) :
    (structureKernelFrameOfFactor p q j h e).hom ≫
        ((Scheme.Modules.restrictFunctor j).map
          (kernel.ι (structurePushforwardMap p)) ≫
            (Scheme.Modules.restrictUnitIso j).hom) =
      e.hom ≫ kernel.ι (structurePushforwardMap q) := by
  rw [← structureKernel_restrict_comp_of_eq_hom_ι p q j h]
  simp only [structureKernelFrameOfFactor, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc]

/-- A typed endomorphism normalization avoids expanding the chosen affine model after transport. -/
theorem structureKernelFrameOfFactor_hom_inclusion_eq {S U X : Scheme}
    (p : S ⟶ X) (q : S ⟶ U) (j : U ⟶ X) [IsOpenImmersion j] (h : q ≫ j = p)
    (e : structureModule U ≅ kernel (structurePushforwardMap q))
    (g : structureModule U ⟶ structureModule U)
    (he : e.hom ≫ kernel.ι (structurePushforwardMap q) = g) :
    (structureKernelFrameOfFactor p q j h e).hom ≫
        ((Scheme.Modules.restrictFunctor j).map
          (kernel.ι (structurePushforwardMap p)) ≫
            (Scheme.Modules.restrictUnitIso j).hom) = g :=
  (structureKernelFrameOfFactor_hom_inclusion p q j h e).trans he

/-- The disjoint-chart frame identifies its inclusion with the identity of the structure sheaf. -/
@[reassoc]
theorem structureKernelDisjointFrame_hom_inclusion {S X U : Scheme}
    (p : S ⟶ X) (j : U ⟶ X) [IsOpenImmersion j]
    (h : p ⁻¹ᵁ j.opensRange = ⊥) :
    (structureKernel_restrict_disjoint p j h).inv ≫
        ((Scheme.Modules.restrictFunctor j).map
          (kernel.ι (structurePushforwardMap p)) ≫
            (Scheme.Modules.restrictUnitIso j).hom) = 𝟙 (structureModule U) := by
  rw [← structureKernel_restrict_disjoint_hom p j h]
  exact Iso.inv_hom_id _


end LeBrunSalamon.P1Ideal
/- END checked component ideal_chart_core.lean -/

/- BEGIN checked component ideal_scalar_restriction.lean -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace LeBrunSalamon.P1Ideal

abbrev affineStructureModule (R : CommRingCat) : (Spec R).Modules :=
  SheafOfModules.unit (Spec R).ringCatSheaf

/-- Multiplication by a ring element on the actual affine structure sheaf. -/
def affineScalarEnd {R : CommRingCat} (r : R) :
    affineStructureModule R ⟶ affineStructureModule R :=
  (tilde.functor R).map (ModuleCat.ofHom (LinearMap.mulRight R r))

theorem tilde_toOpen_self_apply {R : CommRingCat} (U : (Spec R).Opens) (r : R) :
    tilde.toOpen (ModuleCat.of R R) U r =
      (Spec R).presheaf.map U.leTop.op ((Scheme.ΓSpecIso R).inv r) := rfl

theorem affineScalarEnd_app_one {R : CommRingCat} (r : R) (U : (Spec R).Opens) :
    (affineScalarEnd r).app U (1 : Γ(Spec R, U)) =
      (Spec R).presheaf.map U.leTop.op ((Scheme.ΓSpecIso R).inv r) := by
  have h := congrArg
    (fun f : ModuleCat.of R R ⟶
      (modulesSpecToSheaf.obj (tilde (ModuleCat.of R R))).presheaf.obj (Opposite.op U) =>
        f 1)
    (tilde.toOpen_map_app (ModuleCat.ofHom (LinearMap.mulRight R r)) U)
  change (affineScalarEnd r).app U (tilde.toOpen (ModuleCat.of R R) U 1) =
    tilde.toOpen (ModuleCat.of R R) U (1 * r) at h
  change (affineScalarEnd r).app U
      ((Spec R).presheaf.map U.leTop.op ((Scheme.ΓSpecIso R).inv 1)) =
    (Spec R).presheaf.map U.leTop.op ((Scheme.ΓSpecIso R).inv (1 * r)) at h
  simpa only [map_one, one_mul] using h

theorem affineScalarEnd_app {R : CommRingCat} (r : R) (U : (Spec R).Opens)
    (x : Γ(affineStructureModule R, U)) :
    (affineScalarEnd r).app U x = r • x := by
  have h := (affineScalarEnd r).app_smul (U := U) (show Γ(Spec R, U) from x)
    (1 : Γ(Spec R, U))
  rw [affineScalarEnd_app_one] at h
  simpa only [smul_eq_mul, mul_one, Scheme.Modules.smul_Spec_def, mul_comm] using h

/-- Restriction to an affine open transports multiplication through the actual ring homomorphism. -/
@[reassoc]
theorem affineScalarEnd_restrict {R S : CommRingCat} (φ : R ⟶ S)
    [IsOpenImmersion (Spec.map φ)] (r : R) :
    (Scheme.Modules.restrictFunctor (Spec.map φ)).map (affineScalarEnd r) ≫
        (Scheme.Modules.restrictUnitIso (Spec.map φ)).hom =
      (Scheme.Modules.restrictUnitIso (Spec.map φ)).hom ≫ affineScalarEnd (φ r) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  let M : (Spec R).Modules := SheafOfModules.unit (Spec R).ringCatSheaf
  let e := (Scheme.Modules.restrictUnitIso (Spec.map φ)).hom
  have hx := Scheme.Modules.restrictAppIso_smul_Spec (M := M) φ r x
  have he := ((modulesSpecToSheaf.map e).hom.app (Opposite.op U)).hom.map_smul (φ r) x
  change e.app U ((affineScalarEnd r).app (Spec.map φ ''ᵁ U) x) =
    (affineScalarEnd (φ r)).app U (e.app U x)
  rw [affineScalarEnd_app, affineScalarEnd_app]
  change e.app U
      ((M.restrictAppIso (Spec.map φ) U).hom
        (φ r • x)) = (φ r) • e.app U x at he
  rw [hx] at he
  exact he

@[simp]
theorem affineScalarEnd_one {R : CommRingCat} :
    affineScalarEnd (1 : R) = 𝟙 _ := by
  have h : ModuleCat.ofHom (LinearMap.mulRight R (1 : R)) = 𝟙 (ModuleCat.of R R) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact mul_one x
  change (tilde.functor R).map (ModuleCat.ofHom (LinearMap.mulRight R (1 : R))) = _
  rw [h]
  exact (tilde.functor R).map_id (ModuleCat.of R R)

@[simp]
theorem affineScalarEnd_comp {R : CommRingCat} (r s : R) :
    affineScalarEnd r ≫ affineScalarEnd s = affineScalarEnd (r * s) := by
  rw [affineScalarEnd, affineScalarEnd, affineScalarEnd, ← Functor.map_comp]
  apply congrArg ((tilde.functor R).map)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact mul_assoc x r s

/-- A unit on an affine scheme acts by an actual structure-sheaf automorphism. -/
def affineScalarIso {R : CommRingCat} (u : Rˣ) :
    affineStructureModule R ≅ affineStructureModule R where
  hom := affineScalarEnd (u : R)
  inv := affineScalarEnd (↑u⁻¹ : R)
  hom_inv_id := by rw [affineScalarEnd_comp, Units.mul_inv, affineScalarEnd_one]
  inv_hom_id := by rw [affineScalarEnd_comp, Units.inv_mul, affineScalarEnd_one]


end LeBrunSalamon.P1Ideal
/- END checked component ideal_scalar_restriction.lean -/

/- BEGIN checked component ideal_restriction_coherence.lean -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace LeBrunSalamon.P1Ideal

/-- The unit comparison is the structure-sheaf isomorphism of the open immersion. -/
@[simp]
theorem restrictUnitIso_hom_app_apply {X Y : Scheme} (f : X ⟶ Y)
    [IsOpenImmersion f] (U : X.Opens) (x : Γ(Y, f ''ᵁ U)) :
    ((Scheme.Modules.restrictUnitIso f).hom).app U x = (f.appIso U).hom x := rfl

/-- Unit comparison is compatible with successive restrictions along open immersions. -/
@[reassoc]
theorem restrictUnitIso_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    (Scheme.Modules.restrictFunctorComp f g).hom.app (.unit Z.ringCatSheaf) ≫
        (Scheme.Modules.restrictFunctor f).map (Scheme.Modules.restrictUnitIso g).hom ≫
          (Scheme.Modules.restrictUnitIso f).hom =
      (Scheme.Modules.restrictUnitIso (f ≫ g)).hom := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change (f.appIso U).hom
      ((g.appIso (f ''ᵁ U)).hom
        (Z.presheaf.map (eqToHom (by simp)).op x)) =
    ((f ≫ g).appIso U).hom x
  rw [Scheme.Hom.comp_appIso]
  rfl

/-- Unit comparison is independent of the presentation of an open immersion. -/
@[reassoc]
theorem restrictUnitIso_congr {X Y : Scheme} {f g : X ⟶ Y}
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) :
    (Scheme.Modules.restrictFunctorCongr h).hom.app (.unit Y.ringCatSheaf) ≫
        (Scheme.Modules.restrictUnitIso g).hom =
      (Scheme.Modules.restrictUnitIso f).hom := by
  subst g
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change (f.appIso U).hom (Y.presheaf.map (eqToHom rfl).op x) = (f.appIso U).hom x
  simp

/-- The inclusion of a restricted ideal-like module into the local structure sheaf. -/
def restrictedInclusion {X Y : Scheme} (E : Y.Modules)
    (ι : E ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (f : X ⟶ Y) [IsOpenImmersion f] :
    E.restrict f ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (Scheme.Modules.restrictFunctor f).map ι ≫
    (Scheme.Modules.restrictUnitIso f).hom

/-- Actual inclusions commute with the canonical comparison of iterated restrictions. -/
@[reassoc]
theorem restrictedInclusion_comp {X Y Z : Scheme} (E : Z.Modules)
    (ι : E ⟶ SheafOfModules.unit Z.ringCatSheaf)
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g] :
    (Scheme.Modules.restrictFunctorComp f g).hom.app E ≫
        restrictedInclusion (E.restrict g) (restrictedInclusion E ι g) f =
      restrictedInclusion E ι (f ≫ g) := by
  simp only [restrictedInclusion, Functor.map_comp, Category.assoc]
  have h := (Scheme.Modules.restrictFunctorComp f g).hom.naturality ι
  change (Scheme.Modules.restrictFunctor (f ≫ g)).map ι ≫
      (Scheme.Modules.restrictFunctorComp f g).hom.app (.unit Z.ringCatSheaf) =
    (Scheme.Modules.restrictFunctorComp f g).hom.app E ≫
      (Scheme.Modules.restrictFunctor f).map ((Scheme.Modules.restrictFunctor g).map ι) at h
  rw [← Category.assoc, ← Category.assoc, ← h]
  simp only [Category.assoc, restrictUnitIso_comp]

/-- Actual inclusions commute with restriction along equal open immersions. -/
@[reassoc]
theorem restrictedInclusion_congr {X Y : Scheme} (E : Y.Modules)
    (ι : E ⟶ SheafOfModules.unit Y.ringCatSheaf)
    {f g : X ⟶ Y} [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) :
    (Scheme.Modules.restrictFunctorCongr h).hom.app E ≫
        restrictedInclusion E ι g = restrictedInclusion E ι f := by
  unfold restrictedInclusion
  rw [← Category.assoc, ← (Scheme.Modules.restrictFunctorCongr h).hom.naturality ι,
    Category.assoc, restrictUnitIso_congr]

/-- Restrict a local frame and compare it to the one-step restriction of the global module. -/
def restrictedFrame {X Y Z : Scheme} (E : Z.Modules)
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g]
    (e : SheafOfModules.unit Y.ringCatSheaf ≅ E.restrict g) :
    SheafOfModules.unit X.ringCatSheaf ≅ E.restrict (f ≫ g) :=
  (Scheme.Modules.restrictUnitIso f).symm ≪≫
    (Scheme.Modules.restrictFunctor f).mapIso e ≪≫
      ((Scheme.Modules.restrictFunctorComp f g).app E).symm

/-- The restricted frame has the restriction of the original inclusion map. -/
@[reassoc]
theorem restrictedFrame_hom_inclusion {X Y Z : Scheme} (E : Z.Modules)
    (ι : E ⟶ SheafOfModules.unit Z.ringCatSheaf)
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g]
    (e : SheafOfModules.unit Y.ringCatSheaf ≅ E.restrict g) :
    (restrictedFrame E f g e).hom ≫ restrictedInclusion E ι (f ≫ g) =
      (Scheme.Modules.restrictUnitIso f).inv ≫
        (Scheme.Modules.restrictFunctor f).map (e.hom ≫ restrictedInclusion E ι g) ≫
          (Scheme.Modules.restrictUnitIso f).hom := by
  rw [← restrictedInclusion_comp E ι f g]
  simp [restrictedFrame, restrictedInclusion, Functor.map_comp, Category.assoc]


end LeBrunSalamon.P1Ideal
/- END checked component ideal_restriction_coherence.lean -/

/- BEGIN checked component ideal_overlap_geometry.lean -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped LaurentPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LeBrunSalamon.P1Charts

/-- The first-chart projection of the Laurent-coordinate overlap. -/
def polynomialOverlapToZero :
    Spec (CommRingCat.of ℂ[T;T⁻¹]) ⟶ Spec (CommRingCat.of (Polynomial ℂ)) :=
  Spec.map (CommRingCat.ofHom
    (Polynomial.toLaurent : Polynomial ℂ →+* ℂ[T;T⁻¹]))

/-- The second-chart projection substitutes the inverse Laurent coordinate. -/
def polynomialOverlapToOne :
    Spec (CommRingCat.of ℂ[T;T⁻¹]) ⟶ Spec (CommRingCat.of (Polynomial ℂ)) :=
  Spec.map (CommRingCat.ofHom
    (LaurentPolynomial.invert.toRingHom.comp
      (Polynomial.toLaurent : Polynomial ℂ →+* ℂ[T;T⁻¹])))

instance polynomialOverlapToZero_isOpenImmersion :
    IsOpenImmersion polynomialOverlapToZero :=
  IsOpenImmersion.of_isLocalization (R := Polynomial ℂ)
    (S := ℂ[T;T⁻¹]) Polynomial.X

instance polynomialOverlapToOne_isOpenImmersion :
    IsOpenImmersion polynomialOverlapToOne := by
  letI : IsIso (CommRingCat.ofHom
      (LaurentPolynomial.invert.toRingHom : ℂ[T;T⁻¹] →+* ℂ[T;T⁻¹])) :=
    inferInstanceAs (IsIso
      ((LaurentPolynomial.invert.toRingEquiv :
        ℂ[T;T⁻¹] ≃+* ℂ[T;T⁻¹]).toCommRingCatIso.hom))
  change IsOpenImmersion (Spec.map
    (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial ℂ →+* ℂ[T;T⁻¹]) ≫
      CommRingCat.ofHom LaurentPolynomial.invert.toRingHom))
  rw [Spec.map_comp]
  change IsOpenImmersion
    (Spec.map (CommRingCat.ofHom
      (LaurentPolynomial.invert.toRingHom : ℂ[T;T⁻¹] →+* ℂ[T;T⁻¹])) ≫
        polynomialOverlapToZero)
  infer_instance

theorem polynomialOverlapToZero_comp_chart :
    polynomialOverlapToZero ≫ polynomialChartInclusion 0 =
      Spec.map (CommRingCat.ofHom overlapRingEquiv.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom chartZeroToOverlap) ≫ chartInclusion 0) := by
  have h : CommRingCat.ofHom (chartToPolynomial 0) ≫
      CommRingCat.ofHom (Polynomial.toLaurent : Polynomial ℂ →+* ℂ[T;T⁻¹]) =
      CommRingCat.ofHom chartZeroToOverlap ≫
        CommRingCat.ofHom overlapRingEquiv.toRingHom := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact (overlapRingEquiv_chartZero x).symm
  change Spec.map (CommRingCat.ofHom
      (Polynomial.toLaurent : Polynomial ℂ →+* ℂ[T;T⁻¹])) ≫
      (Spec.map (CommRingCat.ofHom (chartToPolynomial 0)) ≫ chartInclusion 0) = _
  simp only [← Category.assoc, ← Spec.map_comp, h]

theorem polynomialOverlapToOne_comp_chart :
    polynomialOverlapToOne ≫ polynomialChartInclusion 1 =
      Spec.map (CommRingCat.ofHom overlapRingEquiv.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom chartOneToOverlap) ≫ chartInclusion 1) := by
  have h : CommRingCat.ofHom (chartToPolynomial 1) ≫
      CommRingCat.ofHom
        (LaurentPolynomial.invert.toRingHom.comp
          (Polynomial.toLaurent : Polynomial ℂ →+* ℂ[T;T⁻¹])) =
      CommRingCat.ofHom chartOneToOverlap ≫
        CommRingCat.ofHom overlapRingEquiv.toRingHom := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact (overlapRingEquiv_chartOne x).symm
  change Spec.map (CommRingCat.ofHom
      (LaurentPolynomial.invert.toRingHom.comp
        (Polynomial.toLaurent : Polynomial ℂ →+* ℂ[T;T⁻¹]))) ≫
      (Spec.map (CommRingCat.ofHom (chartToPolynomial 1)) ≫ chartInclusion 1) = _
  simp only [← Category.assoc, ← Spec.map_comp, h]

/-- The two polynomial-chart projections agree on the actual Laurent overlap in Proj. -/
theorem polynomialOverlap_condition :
    polynomialOverlapToZero ≫ polynomialChartInclusion 0 =
      polynomialOverlapToOne ≫ polynomialChartInclusion 1 := by
  rw [polynomialOverlapToZero_comp_chart, polynomialOverlapToOne_comp_chart,
    overlapInclusions_comp]


end LeBrunSalamon.P1Charts
/- END checked component ideal_overlap_geometry.lean -/

/- BEGIN checked component ideal_overlap_cover.lean -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped LaurentPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LeBrunSalamon.P1Charts

instance homogeneousOverlap_isOpenImmersion :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom chartZeroToOverlap) ≫ chartInclusion 0) := by
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (HomogeneousLocalization.awayMap grading (variable_degree 1) rfl)) ≫
        Proj.awayι grading (MvPolynomial.X 0) (variable_degree 0) (by decide))
  rw [Proj.SpecMap_awayMap_awayι]
  infer_instance

/-- The homogeneous-localization overlap has exactly the intersection of the two chart ranges. -/
theorem homogeneousOverlap_range :
    (Spec.map (CommRingCat.ofHom chartZeroToOverlap) ≫ chartInclusion 0).opensRange =
      chartOpen 0 ⊓ chartOpen 1 := by
  simp only [chartZeroToOverlap, chartInclusion, chartOpen,
    Proj.SpecMap_awayMap_awayι, Proj.opensRange_awayι, Proj.basicOpen_mul]

/-- The Laurent-coordinate overlap is the entire chart intersection. -/
theorem polynomialOverlap_range :
    (polynomialOverlapToZero ≫ polynomialChartInclusion 0).opensRange =
      chartOpen 0 ⊓ chartOpen 1 := by
  letI : IsIso (CommRingCat.ofHom overlapRingEquiv.toRingHom) :=
    inferInstanceAs (IsIso overlapRingEquiv.toCommRingCatIso.hom)
  have h := (Scheme.Hom.opensRange_comp_of_isIso
    (Spec.map (CommRingCat.ofHom overlapRingEquiv.toRingHom))
    (Spec.map (CommRingCat.ofHom chartZeroToOverlap) ≫ chartInclusion 0)).trans
      homogeneousOverlap_range
  simpa only [← polynomialOverlapToZero_comp_chart] using h

/-- The Laurent-coordinate scheme is isomorphic to the actual open chart intersection. -/
def polynomialOverlapIsoInf :
    Spec (CommRingCat.of ℂ[T;T⁻¹]) ≅ (chartOpen 0 ⊓ chartOpen 1).toScheme :=
  IsOpenImmersion.isoOfRangeEq
    (polynomialOverlapToZero ≫ polynomialChartInclusion 0) (chartOpen 0 ⊓ chartOpen 1).ι
    (by
      change (polynomialOverlapToZero ≫ polynomialChartInclusion 0).opensRange.1 =
        (chartOpen 0 ⊓ chartOpen 1).ι.opensRange.1
      rw [polynomialOverlap_range, Scheme.Opens.opensRange_ι])

@[reassoc]
theorem polynomialOverlapIsoInf_hom_ι :
    polynomialOverlapIsoInf.hom ≫ (chartOpen 0 ⊓ chartOpen 1).ι =
      polynomialOverlapToZero ≫ polynomialChartInclusion 0 :=
  IsOpenImmersion.isoOfRangeEq_hom_fac ..

/-- The first projection of that actual intersection agrees with the Laurent projection. -/
@[reassoc]
theorem polynomialOverlapIsoInf_toZero :
    polynomialOverlapIsoInf.hom ≫
        lineScheme.homOfLE (inf_le_left : chartOpen 0 ⊓ chartOpen 1 ≤ chartOpen 0) ≫
          (polynomialChartIso 0).hom = polynomialOverlapToZero := by
  rw [← cancel_mono (polynomialChartInclusion 0)]
  simp only [Category.assoc, polynomialChartInclusion, Iso.hom_inv_id_assoc,
    Scheme.homOfLE_ι, polynomialOverlapIsoInf_hom_ι]

/-- The second projection agrees as well, including its inverse-coordinate identification. -/
@[reassoc]
theorem polynomialOverlapIsoInf_toOne :
    polynomialOverlapIsoInf.hom ≫
        lineScheme.homOfLE (inf_le_right : chartOpen 0 ⊓ chartOpen 1 ≤ chartOpen 1) ≫
          (polynomialChartIso 1).hom = polynomialOverlapToOne := by
  rw [← cancel_mono (polynomialChartInclusion 1)]
  simp only [Category.assoc, polynomialChartInclusion, Iso.hom_inv_id_assoc,
    Scheme.homOfLE_ι, polynomialOverlapIsoInf_hom_ι]
  exact polynomialOverlap_condition


end LeBrunSalamon.P1Charts
/- END checked component ideal_overlap_cover.lean -/

/- BEGIN checked component ideal_local_gluing.lean -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwentyFive

namespace LeBrunSalamon.P1Ideal

open HomConstruction

/-- A global module morphism viewed on every subopen of one open. -/
def localSectionOfHom {X : Scheme} {E F : OModule X} (f : E ⟶ F) (U : X.Opens) :
    Section E F U :=
  (PresheafOfModules.pushforward₀ (Over.forget U) X.ringCatSheaf.obj).map f.val

@[simp]
theorem localSectionOfHom_app {X : Scheme} {E F : OModule X} (f : E ⟶ F)
    (U : X.Opens) (V : (Over U)ᵒᵖ) :
    (localSectionOfHom f U).app V = f.val.app (op V.unop.left) := rfl

@[simp]
theorem localSectionOfHom_restrict {X : Scheme} {E F : OModule X}
    (f : E ⟶ F) {U V : X.Opens} (i : V ⟶ U) :
    restrictSection i (localSectionOfHom f U) = localSectionOfHom f V := by
  apply PresheafOfModules.hom_ext
  intro W
  rfl

@[simp]
theorem localSectionOfHom_id {X : Scheme} (E : OModule X) (U : X.Opens) :
    localSectionOfHom (𝟙 E) U = 𝟙 (restricted E U) := rfl

@[simp]
theorem localSectionOfHom_comp {X : Scheme} {E F G : OModule X}
    (f : E ⟶ F) (g : F ⟶ G) (U : X.Opens) :
    localSectionOfHom (f ≫ g) U = localSectionOfHom f U ≫ localSectionOfHom g U := rfl

/-- A section of the genuine local-Hom sheaf on the whole space is a global morphism. -/
def homOfTopSection {X : Scheme} {E F : OModule X} (φ : Section E F ⊤) : E ⟶ F :=
  ⟨{
    app U := φ.app (op (Over.mk (homOfLE (show U.unop ≤ ⊤ from le_top))))
    naturality := by
      intro U V i
      let j : Over.mk (homOfLE (show V.unop ≤ ⊤ from le_top)) ⟶
          Over.mk (homOfLE (show U.unop ≤ ⊤ from le_top)) := Over.homMk i.unop
      exact φ.naturality j.op }⟩

@[simp]
theorem homOfTopSection_app {X : Scheme} {E F : OModule X}
    (φ : Section E F ⊤) (U : X.Opens) :
    (homOfTopSection φ).val.app (op U) =
      φ.app (op (Over.mk (homOfLE (show U ≤ ⊤ from le_top)))) := rfl

@[simp]
theorem homOfTopSection_localSection {X : Scheme} {E F : OModule X} (f : E ⟶ F) :
    homOfTopSection (localSectionOfHom f ⊤) = f := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  rfl

@[simp]
theorem localSectionOfHom_homOfTopSection {X : Scheme} {E F : OModule X}
    (φ : Section E F ⊤) (U : X.Opens) :
    localSectionOfHom (homOfTopSection φ) U = restrictSection U.leTop φ := by
  apply PresheafOfModules.hom_ext
  intro V
  rfl

/-- The explicit whole-space local-Hom equivalence. -/
def topSectionHomEquiv {X : Scheme} (E F : OModule X) : Section E F ⊤ ≃ (E ⟶ F) where
  toFun := homOfTopSection
  invFun f := localSectionOfHom f ⊤
  left_inv φ := by
    change localSectionOfHom (homOfTopSection φ) ⊤ = φ
    rw [localSectionOfHom_homOfTopSection]
    apply PresheafOfModules.hom_ext
    intro V
    rfl
  right_inv := homOfTopSection_localSection

/-- The underlying additive sheaf of the genuine local module-Hom object. -/
def localHomSheaf {X : Scheme} (E F : OModule X) : TopCat.Sheaf AddCommGrpCat X :=
  ⟨(HomConstruction.object E F).val.presheaf, (HomConstruction.object E F).isSheaf⟩

/-- Compatible local module morphisms glue uniquely over any open cover. -/
theorem existsUnique_localHom_gluing {X : Scheme} {E F : OModule X}
    {I : Type} (U : I → X.Opens) (hcover : iSup U = ⊤)
    (sf : ∀ i, Section E F (U i))
    (h : ∀ i j,
      restrictSection (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) (sf i) =
        restrictSection (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)) (sf j)) :
    ∃! f : E ⟶ F, ∀ i, localSectionOfHom f (U i) = sf i := by
  have hc : TopCat.Presheaf.IsCompatible (localHomSheaf E F).obj U sf := h
  obtain ⟨s, hs, hu⟩ :=
    (localHomSheaf E F).existsUnique_gluing' U ⊤ (fun i => (U i).leTop)
      (by rw [hcover]) sf hc
  refine ⟨homOfTopSection s, ?_, ?_⟩
  · intro i
    exact (localSectionOfHom_homOfTopSection s (U i)).trans (hs i)
  · intro g hg
    have he : localSectionOfHom g ⊤ = s := hu _ (by
      intro i
      change restrictSection (U i).leTop (localSectionOfHom g ⊤) = sf i
      rw [localSectionOfHom_restrict, hg i])
    simpa only [homOfTopSection_localSection] using congrArg homOfTopSection he

/-- Local equality on an open cover detects equality of actual module morphisms. -/
theorem hom_ext_of_localSections {X : Scheme} {E F : OModule X}
    {I : Type} (U : I → X.Opens) (hcover : iSup U = ⊤)
    (f g : E ⟶ F) (h : ∀ i, localSectionOfHom f (U i) = localSectionOfHom g (U i)) :
    f = g := by
  apply (topSectionHomEquiv E F).symm.injective
  apply (localHomSheaf E F).eq_of_locally_eq' U ⊤ (fun i => (U i).leTop)
    (by rw [hcover])
  intro i
  change restrictSection (U i).leTop (localSectionOfHom f ⊤) =
    restrictSection (U i).leTop (localSectionOfHom g ⊤)
  simpa only [localSectionOfHom_restrict] using h i

/-- The unique actual morphism obtained by gluing compatible local maps. -/
def glueLocalHom {X : Scheme} {E F : OModule X}
    {I : Type} (U : I → X.Opens) (hcover : iSup U = ⊤)
    (sf : ∀ i, Section E F (U i))
    (h : ∀ i j,
      restrictSection (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) (sf i) =
        restrictSection (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)) (sf j)) : E ⟶ F :=
  Classical.choose (existsUnique_localHom_gluing U hcover sf h).exists

@[simp]
theorem glueLocalHom_local {X : Scheme} {E F : OModule X}
    {I : Type} (U : I → X.Opens) (hcover : iSup U = ⊤)
    (sf : ∀ i, Section E F (U i))
    (h : ∀ i j,
      restrictSection (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) (sf i) =
        restrictSection (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)) (sf j)) (i : I) :
    localSectionOfHom (glueLocalHom U hcover sf h) (U i) = sf i :=
  Classical.choose_spec (existsUnique_localHom_gluing U hcover sf h).exists i

/-- Mutually inverse compatible local maps glue to an actual global module isomorphism. -/
def glueLocalIso {X : Scheme} {E F : OModule X}
    {I : Type} (U : I → X.Opens) (hcover : iSup U = ⊤)
    (sf : ∀ i, Section E F (U i)) (sg : ∀ i, Section F E (U i))
    (hf : ∀ i j,
      restrictSection (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) (sf i) =
        restrictSection (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)) (sf j))
    (hg : ∀ i j,
      restrictSection (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) (sg i) =
        restrictSection (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)) (sg j))
    (hfg : ∀ i, sf i ≫ sg i = 𝟙 (restricted E (U i)))
    (hgf : ∀ i, sg i ≫ sf i = 𝟙 (restricted F (U i))) : E ≅ F where
  hom := glueLocalHom U hcover sf hf
  inv := glueLocalHom U hcover sg hg
  hom_inv_id := by
    apply hom_ext_of_localSections U hcover
    intro i
    rw [localSectionOfHom_comp, glueLocalHom_local, glueLocalHom_local,
      localSectionOfHom_id, hfg i]
  inv_hom_id := by
    apply hom_ext_of_localSections U hcover
    intro i
    rw [localSectionOfHom_comp, glueLocalHom_local, glueLocalHom_local,
      localSectionOfHom_id, hgf i]


end LeBrunSalamon.P1Ideal
/- END checked component ideal_local_gluing.lean -/

/- BEGIN checked component ideal_over_gluing.lean -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwentyFive

namespace LeBrunSalamon.P1Ideal

open HomConstruction

/-- Restrict an actual local module isomorphism, with the canonical over-site comparisons. -/
def restrictOverIso {X : Scheme} {E F : OModule X} {U V : X.Opens}
    (i : V ⟶ U) (e : E.over U ≅ F.over U) : E.over V ≅ F.over V :=
  ((SheafOfModules.overFunctorMap X.ringCatSheaf i).app E).symm ≪≫
    (SheafOfModules.overMap X.ringCatSheaf i).mapIso e ≪≫
      (SheafOfModules.overFunctorMap X.ringCatSheaf i).app F

/-- The local-Hom encoding of an isomorphism's forward map commutes with restriction. -/
theorem sectionOfOverIso_hom_restrict {X : Scheme} {E F : OModule X} {U V : X.Opens}
    (i : V ⟶ U) (e : E.over U ≅ F.over U) :
    restrictSection i ((sectionOverEquiv E F U).symm e.hom) =
      (sectionOverEquiv E F V).symm (restrictOverIso i e).hom := by
  apply (sectionOverEquiv E F V).injective
  rw [sectionOverEquiv_restrict, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

/-- The same statement for inverse maps, so one cocycle suffices for isomorphism gluing. -/
theorem sectionOfOverIso_inv_restrict {X : Scheme} {E F : OModule X} {U V : X.Opens}
    (i : V ⟶ U) (e : E.over U ≅ F.over U) :
    restrictSection i ((sectionOverEquiv F E U).symm e.inv) =
      (sectionOverEquiv F E V).symm (restrictOverIso i e).inv := by
  apply (sectionOverEquiv F E V).injective
  rw [sectionOverEquiv_restrict, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

@[simp]
theorem sectionOverEquiv_symm_comp {X : Scheme} {E F G : OModule X} (U : X.Opens)
    (f : E.over U ⟶ F.over U) (g : F.over U ⟶ G.over U) :
    (sectionOverEquiv E F U).symm f ≫ (sectionOverEquiv F G U).symm g =
      (sectionOverEquiv E G U).symm (f ≫ g) := by
  apply PresheafOfModules.hom_ext
  intro V
  rfl

@[simp]
theorem sectionOverEquiv_symm_id {X : Scheme} (E : OModule X) (U : X.Opens) :
    (sectionOverEquiv E E U).symm (𝟙 (E.over U)) = 𝟙 (restricted E U) := by
  apply PresheafOfModules.hom_ext
  intro V
  rfl

/-- Compatible isomorphisms on an arbitrary open cover glue to an actual global isomorphism. -/
def glueOverIso {X : Scheme} {E F : OModule X}
    {I : Type} (U : I → X.Opens) (hcover : iSup U = ⊤)
    (e : ∀ i, E.over (U i) ≅ F.over (U i))
    (h : ∀ i j,
      restrictOverIso (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) (e i) =
        restrictOverIso (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)) (e j)) : E ≅ F :=
  glueLocalIso U hcover
    (fun i => (sectionOverEquiv E F (U i)).symm (e i).hom)
    (fun i => (sectionOverEquiv F E (U i)).symm (e i).inv)
    (by
      intro i j
      rw [sectionOfOverIso_hom_restrict, sectionOfOverIso_hom_restrict, h i j])
    (by
      intro i j
      rw [sectionOfOverIso_inv_restrict, sectionOfOverIso_inv_restrict, h i j])
    (by intro i; simp)
    (by intro i; simp)

/-- The glued forward map recovers each given actual local isomorphism. -/
theorem glueOverIso_hom_local {X : Scheme} {E F : OModule X}
    {I : Type} (U : I → X.Opens) (hcover : iSup U = ⊤)
    (e : ∀ i, E.over (U i) ≅ F.over (U i))
    (h : ∀ i j,
      restrictOverIso (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) (e i) =
        restrictOverIso (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)) (e j)) (i : I) :
    sectionOverEquiv E F (U i)
        (localSectionOfHom (glueOverIso U hcover e h).hom (U i)) = (e i).hom := by
  simp only [glueOverIso, glueLocalIso, glueLocalHom_local, Equiv.apply_symm_apply]

/-- The glued inverse likewise recovers the local inverse map. -/
theorem glueOverIso_inv_local {X : Scheme} {E F : OModule X}
    {I : Type} (U : I → X.Opens) (hcover : iSup U = ⊤)
    (e : ∀ i, E.over (U i) ≅ F.over (U i))
    (h : ∀ i j,
      restrictOverIso (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) (e i) =
        restrictOverIso (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)) (e j)) (i : I) :
    sectionOverEquiv F E (U i)
        (localSectionOfHom (glueOverIso U hcover e h).inv (U i)) = (e i).inv := by
  simp only [glueOverIso, glueLocalIso, glueLocalHom_local, Equiv.apply_symm_apply]


end LeBrunSalamon.P1Ideal
/- END checked component ideal_over_gluing.lean -/


/- BEGIN checked supplement ideal_included_frame.lean -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight

namespace LeBrunSalamon.P1Ideal

/-- A frame and its equation against a specified actual inclusion, retained together. -/
structure IncludedFrame {X : Scheme} (E : OModule X)
    (ι : E ⟶ structureModule X) (g : structureModule X ⟶ structureModule X) where
  frame : structureModule X ≅ E
  inclusion : frame.hom ≫ ι = g

/-- Rewriting the specified endomorphism does not reconstruct the frame. -/
def IncludedFrame.congr {X : Scheme} {E : OModule X}
    {ι : E ⟶ structureModule X} {g g' : structureModule X ⟶ structureModule X}
    (d : IncludedFrame E ι g) (h : g = g') : IncludedFrame E ι g' where
  frame := d.frame
  inclusion := d.inclusion.trans h

/-- Transport a bundled affine frame through the canonical global-kernel restriction comparison. -/
def structureKernelIncludedFrameOfFactor {S U X : Scheme}
    (p : S ⟶ X) (q : S ⟶ U) (j : U ⟶ X) [IsOpenImmersion j] (h : q ≫ j = p)
    (g : structureModule U ⟶ structureModule U)
    (d : IncludedFrame (kernel (structurePushforwardMap q))
      (kernel.ι (structurePushforwardMap q)) g) :
    IncludedFrame ((kernel (structurePushforwardMap p)).restrict j)
      ((Scheme.Modules.restrictFunctor j).map (kernel.ι (structurePushforwardMap p)) ≫
        (Scheme.Modules.restrictUnitIso j).hom) g where
  frame := structureKernelFrameOfFactor p q j h d.frame
  inclusion := structureKernelFrameOfFactor_hom_inclusion_eq p q j h d.frame g d.inclusion

/-- The bundled frame of a chart disjoint from the point has inclusion equal to identity. -/
def structureKernelIncludedFrameOfDisjoint {S X U : Scheme}
    (p : S ⟶ X) (j : U ⟶ X) [IsOpenImmersion j]
    (h : p ⁻¹ᵁ j.opensRange = ⊥) :
    IncludedFrame ((kernel (structurePushforwardMap p)).restrict j)
      ((Scheme.Modules.restrictFunctor j).map (kernel.ι (structurePushforwardMap p)) ≫
        (Scheme.Modules.restrictUnitIso j).hom) (𝟙 (structureModule U)) where
  frame := (structureKernel_restrict_disjoint p j h).symm
  inclusion := structureKernelDisjointFrame_hom_inclusion p j h

/-- The normalized affine finite-point kernel, before any transport to Proj. -/
def affinePointFirstFrameData (a : ℂ) :
    IncludedFrame
      (kernel (structurePushforwardMap
        (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)))))
      (kernel.ι (structurePushforwardMap
        (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)))))
      (affineScalarEnd (R := CommRingCat.of (Polynomial ℂ)) (finiteGeneratorZero a)) :=
  ⟨finitePointFirstFrame a, finitePointFirstFrame_hom_ι a⟩

/-- The normalized second affine kernel keeps its generator 1-a*s in the same certificate. -/
def affinePointSecondFrameData (a : ℂ) (ha : a ≠ 0) :
    IncludedFrame
      (kernel (structurePushforwardMap
        (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a⁻¹)))))
      (kernel.ι (structurePushforwardMap
        (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a⁻¹)))))
      (affineScalarEnd (R := CommRingCat.of (Polynomial ℂ)) (finiteGeneratorOne a)) :=
  ⟨finitePointSecondFrame a ha, finitePointSecondFrame_hom_ι a ha⟩

/-- The affine zero-coordinate kernel with generator exactly X. -/
def affineInfinityFrameData :
    IncludedFrame
      (kernel (structurePushforwardMap
        (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : ℂ))))))
      (kernel.ι (structurePushforwardMap
        (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : ℂ))))))
      (affineScalarEnd (R := CommRingCat.of (Polynomial ℂ)) Polynomial.X) :=
  (affinePointFirstFrameData 0).congr
    (by simp only [finiteGeneratorZero, map_zero, sub_zero])


end LeBrunSalamon.P1Ideal
/- END checked supplement ideal_included_frame.lean -/

/- BEGIN checked supplement ideal_chart_object.lean -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.P1Charts
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LeBrunSalamon.P1Ideal

/-- The actual point ideal restricted to one of the two polynomial charts. -/
abbrev pointIdealOnChart (p : Spec (CommRingCat.of ℂ) ⟶ lineScheme) (i : Fin 2) :
    (Spec (CommRingCat.of (Polynomial ℂ))).Modules :=
  (kernel (structurePushforwardMap p)).restrict (polynomialChartInclusion i)

/-- Its actual inclusion into the chart's structure sheaf. -/
def pointIdealChartInclusion (p : Spec (CommRingCat.of ℂ) ⟶ lineScheme) (i : Fin 2) :
    pointIdealOnChart p i ⟶ structureModule (Spec (CommRingCat.of (Polynomial ℂ))) :=
  (Scheme.Modules.restrictFunctor (polynomialChartInclusion i)).map
      (kernel.ι (structurePushforwardMap p)) ≫
    (Scheme.Modules.restrictUnitIso (polynomialChartInclusion i)).hom


end LeBrunSalamon.P1Ideal
/- END checked supplement ideal_chart_object.lean -/

/- BEGIN checked supplement ideal_normalized_structure.lean -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.P1Charts
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LeBrunSalamon.P1Ideal

/-- Normalized frames of an actual point ideal, with their inclusion equations
and common coordinate-ring transition on the actual overlap. -/
structure NormalizedPointIdealFrames
    (p : Spec (CommRingCat.of ℂ) ⟶ lineScheme) where
  generatorZero : Polynomial ℂ
  generatorOne : Polynomial ℂ
  generatorZero_ne_zero : generatorZero ≠ 0
  generatorOne_ne_zero : generatorOne ≠ 0
  frameZero : structureModule (Spec (CommRingCat.of (Polynomial ℂ))) ≅ pointIdealOnChart p 0
  frameOne : structureModule (Spec (CommRingCat.of (Polynomial ℂ))) ≅ pointIdealOnChart p 1
  frameZero_inclusion : frameZero.hom ≫ pointIdealChartInclusion p 0 =
    affineScalarEnd (R := CommRingCat.of (Polynomial ℂ)) generatorZero
  frameOne_inclusion : frameOne.hom ≫ pointIdealChartInclusion p 1 =
    affineScalarEnd (R := CommRingCat.of (Polynomial ℂ)) generatorOne
  overlap_transition :
    chartOneToOverlap ((chartRingEquiv 1).symm generatorOne) =
      chartOneToOverlap (ratio 1 0) *
        chartZeroToOverlap ((chartRingEquiv 0).symm generatorZero)


end LeBrunSalamon.P1Ideal
/- END checked supplement ideal_normalized_structure.lean -/

/- BEGIN checked supplement ideal_affine_overlap_transport.lean -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace LeBrunSalamon.P1Ideal

/-- The scalar inclusion equation of a frame survives restriction along an affine open. -/
@[reassoc]
theorem restrictedFrame_affine_hom_inclusion {R S : CommRingCat} {Z : Scheme}
    (E : Z.Modules) (ι : E ⟶ SheafOfModules.unit Z.ringCatSheaf)
    (φ : R ⟶ S) [IsOpenImmersion (Spec.map φ)]
    (j : Spec R ⟶ Z) [IsOpenImmersion j]
    (e : affineStructureModule R ≅ E.restrict j) (r : R)
    (h : e.hom ≫ restrictedInclusion E ι j = affineScalarEnd r) :
    (restrictedFrame E (Spec.map φ) j e).hom ≫
        restrictedInclusion E ι (Spec.map φ ≫ j) = affineScalarEnd (φ r) := by
  rw [restrictedFrame_hom_inclusion, h, affineScalarEnd_restrict]
  simp



end LeBrunSalamon.P1Ideal
/- END checked supplement ideal_affine_overlap_transport.lean -/


end PointIdealTransitionAndGluing

namespace LeBrunSalamon.P1Overlap

open Polynomial
open scoped LaurentPolynomial

/-! Algebra on the overlap of the two standard projective-line charts.
The chart coordinates are `t = X₁ / X₀` and `s = X₀ / X₁`, so `s = t⁻¹`.
The results below concern the actual rings `K[t]` and `K[t,t⁻¹]`.
The comparison with the project's scheme sheaves is a separate obligation.
-/

variable {K : Type*} [Field K]

theorem unit_is_monomial (f : K[T;T⁻¹]) (hf : IsUnit f) :
    ∃ (c : K) (d : ℤ), c ≠ 0 ∧ f = LaurentPolynomial.C c * LaurentPolynomial.T d := by
  induction f using LaurentPolynomial.induction_on_mul_T with
  | mul_T p n =>
    have hp : IsUnit p.toLaurent := isUnit_of_mul_isUnit_left hf
    obtain ⟨m, hm⟩ := (IsLocalization.Away.algebraMap_isUnit_iff (S := K[T;T⁻¹])
      (x := (X : K[X]))).mp hp
    obtain ⟨k, _hk, hu⟩ := (dvd_prime_pow (Polynomial.prime_X (R := K)) m).mp hm
    obtain ⟨u, hu⟩ := hu.symm
    obtain ⟨c, hc, hcu⟩ := Polynomial.isUnit_iff.mp u.isUnit
    refine ⟨c, (k : ℤ) - n, hc.ne_zero, ?_⟩
    rw [← hu, ← hcu, map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X_pow]
    rw [mul_comm (LaurentPolynomial.T (k : ℤ)) (LaurentPolynomial.C c),
      LaurentPolynomial.mul_T_assoc, sub_eq_add_neg]

theorem isUnit_iff_monomial (f : K[T;T⁻¹]) :
    IsUnit f ↔ ∃ (c : K) (d : ℤ), c ≠ 0 ∧
      f = LaurentPolynomial.C c * LaurentPolynomial.T d := by
  refine ⟨unit_is_monomial f, ?_⟩
  rintro ⟨c, d, hc, rfl⟩
  exact ((isUnit_iff_ne_zero.mpr hc).map LaurentPolynomial.C).mul
    (LaurentPolynomial.isUnit_T d)

theorem monomial_unique {c e : K} {d k : ℤ} (hc : c ≠ 0) (he : e ≠ 0)
    (h : LaurentPolynomial.C c * LaurentPolynomial.T d =
      LaurentPolynomial.C e * LaurentPolynomial.T k) : c = e ∧ d = k := by
  have hd : d = k := by
    have hd := congrArg LaurentPolynomial.degree h
    simpa [LaurentPolynomial.degree_C_mul_T, hc, he] using hd
  subst k
  refine ⟨?_, rfl⟩
  have hv := congrArg (fun f : K[T;T⁻¹] => f.coeff d) h
  simpa only [← LaurentPolynomial.single_eq_C_mul_T,
    AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] using hv

theorem coeff_toLaurent_nat (p : K[X]) (n : ℕ) :
    p.toLaurent.coeff (n : ℤ) = p.coeff n := by
  exact Finsupp.mapDomain_apply_of_injective
    (show Function.Injective (fun n : ℕ => (n : ℤ)) from Nat.cast_injective)
    p.toFinsupp.coeff n

theorem coeff_toLaurent_neg (p : K[X]) {n : ℤ} (hn : n < 0) :
    p.toLaurent.coeff n = 0 := by
  rw [LaurentPolynomial.coeff_toLaurent]
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨k, hk⟩
  exact (not_le_of_gt hn) (hk ▸ Int.natCast_nonneg k)

theorem coeff_mul_T (f : K[T;T⁻¹]) (d n : ℤ) :
    (f * LaurentPolynomial.T d).coeff n = f.coeff (n - d) := by
  unfold LaurentPolynomial.T
  simpa only [sub_eq_add_neg, mul_one] using
    (AddMonoidAlgebra.coeff_mul_single_apply f 1 d n)

/-- A pair of regular polynomial expressions with transition `t^d`. -/
def Matching (d : ℤ) (p q : K[X]) : Prop :=
  p.toLaurent = LaurentPolynomial.invert q.toLaurent * LaurentPolynomial.T d

theorem matching_coeff (d : ℤ) {p q : K[X]} (h : Matching d p q) (n : ℤ) :
    p.toLaurent.coeff n = q.toLaurent.coeff (d - n) := by
  rw [h, coeff_mul_T, LaurentPolynomial.invert_apply]
  congr 1
  omega

theorem matching_first_injective {d : ℤ} {p q q' : K[X]}
    (h : Matching d p q) (h' : Matching d p q') : q = q' := by
  apply Polynomial.toLaurent_injective
  apply LaurentPolynomial.invert.injective
  exact (LaurentPolynomial.isUnit_T d).mul_right_cancel (h.symm.trans h')

theorem matching_negative {d : ℤ} (hd : d < 0) {p q : K[X]}
    (h : Matching d p q) : p = 0 ∧ q = 0 := by
  have hp : p = 0 := by
    ext n
    rw [← coeff_toLaurent_nat, matching_coeff d h]
    exact coeff_toLaurent_neg q (by omega)
  refine ⟨hp, ?_⟩
  have hz : Matching d p 0 := by simp [Matching, hp]
  exact matching_first_injective h hz

theorem matching_degree_le {d : ℕ} {p q : K[X]} (h : Matching (d : ℤ) p q) :
    p.natDegree ≤ d := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [← coeff_toLaurent_nat, matching_coeff (d : ℤ) h]
  exact coeff_toLaurent_neg q (by omega)

theorem matching_reflect (d : ℕ) (p : K[X]) (hp : p.natDegree ≤ d) :
    Matching (d : ℤ) p (p.reflect d) := by
  have hq : (p.reflect d).natDegree ≤ d :=
    Polynomial.natDegree_reflect_le.trans (max_le le_rfl hp)
  apply LaurentPolynomial.ext
  intro n
  rw [coeff_mul_T, LaurentPolynomial.invert_apply]
  rw [show -(n - (d : ℤ)) = (d : ℤ) - n by omega]
  cases n with
  | ofNat n =>
    change p.toLaurent.coeff (n : ℤ) = (p.reflect d).toLaurent.coeff ((d : ℤ) - (n : ℤ))
    by_cases hn : n ≤ d
    · rw [coeff_toLaurent_nat, ← Int.natCast_sub hn, coeff_toLaurent_nat,
        Polynomial.coeff_reflect, Polynomial.revAt_le (Nat.sub_le d n),
        Nat.sub_sub_self hn]
    · rw [coeff_toLaurent_nat, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
        coeff_toLaurent_neg _ (by omega)]
  | negSucc n =>
    rw [coeff_toLaurent_neg p (by omega)]
    have he : (d : ℤ) - Int.negSucc n = ((d + n + 1 : ℕ) : ℤ) := by omega
    rw [he, coeff_toLaurent_nat, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

theorem matching_iff_reflect (d : ℕ) (p q : K[X]) :
    Matching (d : ℤ) p q ↔ p.natDegree ≤ d ∧ q = p.reflect d := by
  constructor
  · intro h
    have hp := matching_degree_le h
    exact ⟨hp, matching_first_injective h (matching_reflect d p hp)⟩
  · rintro ⟨hp, rfl⟩
    exact matching_reflect d p hp

/-- The algebraic equalizer of the two restriction maps for transition `t^d`. -/
def matchingSpace (d : ℤ) : Submodule K (K[X] × K[X]) where
  carrier := {pq | Matching d pq.1 pq.2}
  zero_mem' := by simp [Matching]
  add_mem' := by
    intro pq rs hpq hrs
    change Matching d (pq.1 + rs.1) (pq.2 + rs.2)
    simp only [Matching, map_add, add_mul]
    rw [hpq, hrs]
  smul_mem' := by
    intro c pq hpq
    change Matching d (c • pq.1) (c • pq.2)
    change Polynomial.toLaurentAlg (c • pq.1) =
      LaurentPolynomial.invert (Polynomial.toLaurentAlg (c • pq.2)) * _
    rw [map_smul, map_smul, map_smul, smul_mul_assoc]
    exact congrArg (c • ·) hpq

theorem matchingSpace_ext {d : ℤ} (a b : matchingSpace (K := K) d)
    (h : a.val.1 = b.val.1) : a = b := by
  apply Subtype.ext
  apply Prod.ext h
  apply matching_first_injective a.property
  have hb : Matching d b.val.1 b.val.2 := b.property
  simpa only [h] using hb

private theorem mem_degreeLT_succ_iff (d : ℕ) (p : K[X]) :
    p ∈ Polynomial.degreeLT K (d + 1) ↔ p.natDegree ≤ d := by
  rw [Polynomial.degreeLT_succ_eq_degreeLE, Polynomial.mem_degreeLE]
  exact Polynomial.natDegree_le_iff_degree_le.symm

/-- The first-chart expression identifies matching sections with degree ≤ d polynomials. -/
def matchingSpaceEquiv (d : ℕ) :
    matchingSpace (K := K) (d : ℤ) ≃ₗ[K] Polynomial.degreeLT K (d + 1) where
  toFun a := ⟨a.val.1, (mem_degreeLT_succ_iff d a.val.1).mpr
    (matching_degree_le a.property)⟩
  invFun p := ⟨(p.val, p.val.reflect d), matching_reflect d p.val
    ((mem_degreeLT_succ_iff d p.val).mp p.property)⟩
  left_inv a := matchingSpace_ext _ _ rfl
  right_inv p := rfl
  map_add' a b := rfl
  map_smul' c a := rfl

theorem matchingSpace_finrank (d : ℕ) :
    Module.finrank K (matchingSpace (K := K) (d : ℤ)) = d + 1 := by
  rw [(matchingSpaceEquiv (K := K) d).finrank_eq]
  simpa using Module.finrank_eq_card_basis (Polynomial.degreeLT.basis K (d + 1))

theorem matchingSpace_subsingleton_of_negative {d : ℤ} (hd : d < 0) :
    Subsingleton (matchingSpace (K := K) d) := by
  refine ⟨fun a b => matchingSpace_ext a b ?_⟩
  exact (matching_negative hd a.property).1.trans (matching_negative hd b.property).1.symm

theorem matchingSpace_finrank_negative {d : ℤ} (hd : d < 0) :
    Module.finrank K (matchingSpace (K := K) d) = 0 := by
  letI := matchingSpace_subsingleton_of_negative (K := K) hd
  exact Module.finrank_zero_of_subsingleton

end LeBrunSalamon.P1Overlap

namespace LeBrunSalamon.P1Overlap

open Polynomial
open scoped LaurentPolynomial

variable {K : Type*} [Field K]

/-- The difference of the two polynomial restriction maps on the overlap. -/
def cechDifference (d : ℤ) : K[X] × K[X] →ₗ[K] K[T;T⁻¹] where
  toFun pq := pq.1.toLaurent - LaurentPolynomial.invert pq.2.toLaurent * LaurentPolynomial.T d
  map_add' pq rs := by
    change (pq.1 + rs.1).toLaurent -
      LaurentPolynomial.invert ((pq.2 + rs.2).toLaurent) * LaurentPolynomial.T d =
      (pq.1.toLaurent - LaurentPolynomial.invert pq.2.toLaurent * LaurentPolynomial.T d) +
      (rs.1.toLaurent - LaurentPolynomial.invert rs.2.toLaurent * LaurentPolynomial.T d)
    rw [map_add, map_add, map_add, add_mul]
    exact (sub_add_sub_comm _ _ _ _).symm
  map_smul' c pq := by
    change Polynomial.toLaurentAlg (c • pq.1) -
      LaurentPolynomial.invert (Polynomial.toLaurentAlg (c • pq.2)) * _ = _
    rw [map_smul, map_smul, map_smul, smul_mul_assoc, smul_sub]
    rfl

theorem cechDifference_kernel (d : ℤ) :
    LinearMap.ker (cechDifference (K := K) d) = matchingSpace d := by
  ext pq
  change pq.1.toLaurent - LaurentPolynomial.invert pq.2.toLaurent *
    LaurentPolynomial.T d = 0 ↔ Matching d pq.1 pq.2
  exact sub_eq_zero

theorem monomial_mem_cechRange (d n : ℤ) (c : K) (hn : 0 ≤ n ∨ n ≤ d) :
    LaurentPolynomial.C c * LaurentPolynomial.T n ∈ LinearMap.range (cechDifference d) := by
  rcases hn with hn | hn
  · refine ⟨(Polynomial.monomial n.toNat c, 0), ?_⟩
    simp only [cechDifference, LinearMap.coe_mk, AddHom.coe_mk, map_zero, zero_mul, sub_zero,
      Polynomial.toLaurent_C_mul_T, Int.toNat_of_nonneg hn]
  · refine ⟨(0, Polynomial.monomial (d - n).toNat (-c)), ?_⟩
    change 0 - LaurentPolynomial.invert ((Polynomial.monomial (d - n).toNat (-c)).toLaurent) *
      LaurentPolynomial.T d = _
    rw [Polynomial.toLaurent_C_mul_T, map_mul, LaurentPolynomial.invert_C,
      LaurentPolynomial.invert_T, LaurentPolynomial.mul_T_assoc]
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hn)]
    have he : -(d - n) + d = n := by omega
    rw [he, map_neg, neg_mul, zero_sub, neg_neg]

theorem cechDifference_surjective (d : ℤ) (hd : -1 ≤ d) :
    Function.Surjective (cechDifference (K := K) d) := by
  intro f
  change f ∈ LinearMap.range (cechDifference d)
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg => exact Submodule.add_mem _ hf hg
  | C_mul_T n c => exact monomial_mem_cechRange d n c (by omega)

theorem cechDifference_surjective_iff (d : ℤ) :
    Function.Surjective (cechDifference (K := K) d) ↔ -1 ≤ d := by
  refine ⟨?_, cechDifference_surjective d⟩
  intro h
  by_contra hd
  have hd' : d < -1 := lt_of_not_ge hd
  obtain ⟨⟨p, q⟩, hpq⟩ := h (LaurentPolynomial.T (-1))
  have hcoeff := congrArg (fun f : K[T;T⁻¹] => f.coeff (-1)) hpq
  change (p.toLaurent - LaurentPolynomial.invert q.toLaurent *
    LaurentPolynomial.T d).coeff (-1) = _ at hcoeff
  simp only [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply] at hcoeff
  rw [coeff_toLaurent_neg p (by omega), coeff_mul_T, LaurentPolynomial.invert_apply] at hcoeff
  rw [coeff_toLaurent_neg q (by omega)] at hcoeff
  simpa [LaurentPolynomial.T_apply] using hcoeff

/-- Evaluation at the origins of the two charts, the points 0 and infinity. -/
def markedEvaluation (d : ℤ) : matchingSpace (K := K) d →ₗ[K] K × K where
  toFun a := (a.val.1.eval 0, a.val.2.eval 0)
  map_add' a b := by ext <;> simp
  map_smul' c a := by ext <;> simp

theorem matching_evaluation_at_infinity {d : ℕ} {p q : K[X]}
    (h : Matching (d : ℤ) p q) : q.eval 0 = p.coeff d := by
  obtain ⟨_, rfl⟩ := (matching_iff_reflect d p q).mp h
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_reflect, Polynomial.revAt_zero]

theorem markedEvaluation_surjective (d : ℕ) (hd : 1 ≤ d) :
    Function.Surjective (markedEvaluation (K := K) (d : ℤ)) := by
  rintro ⟨a, b⟩
  let p : K[X] := Polynomial.C a + Polynomial.monomial d b
  have hp : p.natDegree ≤ d := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    have hno : n ≠ 0 := by omega
    have hnd : d ≠ n := by omega
    simp [p, Polynomial.coeff_C, hno, Polynomial.coeff_monomial, hnd]
  refine ⟨⟨(p, p.reflect d), matching_reflect d p hp⟩, ?_⟩
  apply Prod.ext
  · change p.eval 0 = a
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    simp [p, Polynomial.coeff_C, Polynomial.coeff_monomial, show d ≠ 0 by omega]
  · change (p.reflect d).eval 0 = b
    rw [matching_evaluation_at_infinity (matching_reflect d p hp)]
    simp [p, Polynomial.coeff_C, Polynomial.coeff_monomial, show d ≠ 0 by omega]

theorem markedEvaluation_not_surjective_nonpositive {d : ℤ} (hd : d ≤ 0) :
    ¬ Function.Surjective (markedEvaluation (K := K) d) := by
  intro h
  obtain ⟨a, ha⟩ := h (1, 0)
  have hfirst := congrArg Prod.fst ha
  have hsecond := congrArg Prod.snd ha
  change a.val.1.eval 0 = 1 at hfirst
  change a.val.2.eval 0 = 0 at hsecond
  rcases lt_or_eq_of_le hd with hd | rfl
  · rw [(matching_negative hd a.property).1, Polynomial.eval_zero] at hfirst
    exact zero_ne_one hfirst
  · have hc := matching_coeff 0 a.property 0
    have hc0 : a.val.1.coeff 0 = a.val.2.coeff 0 :=
      (coeff_toLaurent_nat a.val.1 0).symm.trans
        (hc.trans (coeff_toLaurent_nat a.val.2 0))
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_eq_eval_zero,
      hfirst, hsecond] at hc0
    exact one_ne_zero hc0

theorem markedEvaluation_surjective_iff (d : ℤ) :
    Function.Surjective (markedEvaluation (K := K) d) ↔ 1 ≤ d := by
  constructor
  · intro h
    by_contra hd
    exact markedEvaluation_not_surjective_nonpositive (by omega) h
  · intro hd
    have hdn : (d.toNat : ℤ) = d := Int.toNat_of_nonneg (by omega)
    rw [← hdn]
    exact markedEvaluation_surjective d.toNat (by omega)

end LeBrunSalamon.P1Overlap

namespace LeBrunSalamon.P1Overlap

open Polynomial
open scoped LaurentPolynomial

variable {K : Type*} [Field K]

/-- Coefficients of the monomials strictly between degrees `d` and `0`. -/
def gapProjection (d : ℤ) : K[T;T⁻¹] →ₗ[K] (Fin (-d - 1).toNat → K) where
  toFun f i := f.coeff (-(i.val : ℤ) - 1)
  map_add' f g := by ext i; simp
  map_smul' c f := by ext i; simp

theorem gapProjection_surjective (d : ℤ) :
    Function.Surjective (gapProjection (K := K) d) := by
  intro v
  refine ⟨∑ i, AddMonoidAlgebra.single (-(i.val : ℤ) - 1) (v i), ?_⟩
  funext i
  change (∑ j : Fin (-d - 1).toNat,
    AddMonoidAlgebra.single (-(j.val : ℤ) - 1) (v j)).coeff (-(i.val : ℤ) - 1) = v i
  simp only [AddMonoidAlgebra.coeff_sum, Finset.sum_apply',
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hne : -(j.val : ℤ) - 1 ≠ -(i.val : ℤ) - 1 := by
      intro he
      apply hji
      apply Fin.ext
      omega
    simp only [hne, ite_false]
  · simp

theorem gapProjection_kernel (d : ℤ) :
    LinearMap.ker (gapProjection (K := K) d) = LinearMap.range (cechDifference d) := by
  apply le_antisymm
  · intro f hf
    have hgap : gapProjection d f = 0 := hf
    rw [← AddMonoidAlgebra.sum_coeff_single f]
    apply Submodule.sum_mem
    intro n hn
    rw [LaurentPolynomial.single_eq_C_mul_T]
    apply monomial_mem_cechRange
    by_contra hout
    have hnneg : n < 0 := by omega
    have hnd : d < n := by omega
    let i : Fin (-d - 1).toNat := ⟨(-n - 1).toNat, by omega⟩
    have hi := congrFun hgap i
    change f.coeff (-(i.val : ℤ) - 1) = 0 at hi
    have hexp : -(i.val : ℤ) - 1 = n := by dsimp [i]; omega
    rw [hexp] at hi
    exact (Finsupp.mem_support_iff.mp hn) hi
  · rintro f ⟨⟨p, q⟩, rfl⟩
    change gapProjection d (cechDifference d (p, q)) = 0
    funext i
    change (p.toLaurent - LaurentPolynomial.invert q.toLaurent *
      LaurentPolynomial.T d).coeff (-(i.val : ℤ) - 1) = 0
    simp only [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply]
    rw [coeff_toLaurent_neg p (by omega), coeff_mul_T, LaurentPolynomial.invert_apply,
      coeff_toLaurent_neg q (by have hi := i.isLt; omega), sub_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The actual cokernel of the two-chart difference map, with its missing-coefficient coordinates. -/
def cechCokernelEquiv (d : ℤ) :
    (K[T;T⁻¹] ⧸ LinearMap.range (cechDifference (K := K) d)) ≃ₗ[K]
      (Fin (-d - 1).toNat → K) :=
  (Submodule.quotEquivOfEq (LinearMap.range (cechDifference (K := K) d))
    (LinearMap.ker (gapProjection (K := K) d)) (gapProjection_kernel (K := K) d).symm).trans
    ((gapProjection (K := K) d).quotKerEquivOfSurjective (gapProjection_surjective (K := K) d))

theorem cechCokernel_finrank (d : ℤ) :
    Module.finrank K (K[T;T⁻¹] ⧸ LinearMap.range (cechDifference (K := K) d)) =
      (-d - 1).toNat := by
  rw [(cechCokernelEquiv (K := K) d).finrank_eq]
  simp

end LeBrunSalamon.P1Overlap

namespace LeBrunSalamon.P1Overlap

open Polynomial
open scoped LaurentPolynomial

variable {K : Type*} [Field K]

theorem matchingSpace_finrank_all (d : ℤ) :
    Module.finrank K (matchingSpace (K := K) d) = (d + 1).toNat := by
  cases d with
  | ofNat n => simpa using matchingSpace_finrank (K := K) n
  | negSucc n =>
    rw [matchingSpace_finrank_negative (K := K) (by omega)]
    omega

/-- Riemann–Roch for the explicit two-chart complex. Its comparison with sheaf
cohomology is not assumed by this theorem. -/
theorem cechEulerCharacteristic (d : ℤ) :
    (Module.finrank K (matchingSpace (K := K) d) : ℤ) -
      Module.finrank K (K[T;T⁻¹] ⧸ LinearMap.range (cechDifference (K := K) d)) = d + 1 := by
  rw [matchingSpace_finrank_all, cechCokernel_finrank]
  omega

instance matchingSpace_finite (d : ℤ) : Module.Finite K (matchingSpace (K := K) d) := by
  cases d with
  | ofNat n => exact Module.Finite.equiv (matchingSpaceEquiv (K := K) n).symm
  | negSucc n =>
    letI := matchingSpace_subsingleton_of_negative (K := K) (d := Int.negSucc n) (by omega)
    infer_instance

instance cechCokernel_finite (d : ℤ) :
    Module.Finite K (K[T;T⁻¹] ⧸ LinearMap.range (cechDifference (K := K) d)) :=
  Module.Finite.equiv (cechCokernelEquiv (K := K) d).symm

/-- Evaluation at any finite point in the first affine chart. -/
def finitePointEvaluation (d : ℤ) (x : K) : matchingSpace (K := K) d →ₗ[K] K where
  toFun s := s.val.1.eval x
  map_add' a b := by simp
  map_smul' c a := by simp

theorem finitePointEvaluation_surjective (d : ℕ) (x : K) :
    Function.Surjective (finitePointEvaluation (K := K) (d : ℤ) x) := by
  intro c
  refine ⟨⟨(Polynomial.C c, (Polynomial.C c).reflect d),
    matching_reflect d (Polynomial.C c) (by simp)⟩, ?_⟩
  exact Polynomial.eval_C

theorem finitePointEvaluation_surjective_iff (d : ℤ) (x : K) :
    Function.Surjective (finitePointEvaluation (K := K) d x) ↔ 0 ≤ d := by
  constructor
  · intro h
    by_contra hd
    obtain ⟨s, hs⟩ := h 1
    change s.val.1.eval x = 1 at hs
    rw [(matching_negative (lt_of_not_ge hd) s.property).1, Polynomial.eval_zero] at hs
    exact zero_ne_one hs
  · intro hd
    rw [← Int.toNat_of_nonneg hd]
    exact finitePointEvaluation_surjective d.toNat x

end LeBrunSalamon.P1Overlap


namespace LeBrunSalamon.P1Charts

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.Skeleton

/-- A coordinate evaluation, with the actual canonical complex-base equation. -/
def markedPoint (i : Fin 2) (c : ℂ) : ProjectiveLinePoint canonicalProjectiveLine where
  map := pointMap i c
  overC := pointMap_overC i c

end LeBrunSalamon.P1Charts



/-!
# Phase 32 -- genuine O(d) on P1 and splitting statements

O(1) is the DUAL of the ideal of an actual rational point of P1. Consequently O(d) is no longer an
arbitrary supplied line bundle. Local freeness of the point ideal is now proved using the actual affine charts.
Identification with the usual Serre twist and the Birkhoff--Grothendieck theorem remain obligations. The marked point merely chooses an
isomorphic representative of O(1).
-/

/-! Actual normalized point ideals and the gluing of their comparisons. -/

/- BEGIN checked continuation frames_chart_transport.lean -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.P1Charts
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LeBrunSalamon.P1Ideal

/-- A specified affine factorization transfers its normalized kernel frame to
the actual restriction of the global point ideal on a polynomial chart. -/
def pointIdealChartIncludedFrameOfFactor
    (p : Spec (CommRingCat.of ℂ) ⟶ lineScheme) (i : Fin 2)
    (q : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of (Polynomial ℂ)))
    (h : q ≫ polynomialChartInclusion i = p) (g : Polynomial ℂ)
    (d : IncludedFrame (kernel (structurePushforwardMap q))
      (kernel.ι (structurePushforwardMap q))
      (affineScalarEnd (R := CommRingCat.of (Polynomial ℂ)) g)) :
    IncludedFrame (pointIdealOnChart p i) (pointIdealChartInclusion p i)
      (affineScalarEnd (R := CommRingCat.of (Polynomial ℂ)) g) :=
  structureKernelIncludedFrameOfFactor
    (S := Spec (CommRingCat.of ℂ))
    (U := Spec (CommRingCat.of (Polynomial ℂ))) (X := lineScheme)
    p q (polynomialChartInclusion i) h
    (affineScalarEnd (R := CommRingCat.of (Polynomial ℂ)) g) d

/-- A polynomial chart missing the specified point has the actual identity
inclusion under its canonical kernel frame. -/
def pointIdealChartIncludedFrameOfDisjoint
    (p : Spec (CommRingCat.of ℂ) ⟶ lineScheme) (i : Fin 2)
    (h : p ⁻¹ᵁ (polynomialChartInclusion i).opensRange = ⊥) :
    IncludedFrame (pointIdealOnChart p i) (pointIdealChartInclusion p i)
      (𝟙 (structureModule (Spec (CommRingCat.of (Polynomial ℂ))))) :=
  structureKernelIncludedFrameOfDisjoint
    (S := Spec (CommRingCat.of ℂ)) (X := lineScheme)
    (U := Spec (CommRingCat.of (Polynomial ℂ)))
    p (polynomialChartInclusion i) h

end LeBrunSalamon.P1Ideal

end
/- END checked continuation frames_chart_transport.lean -/

/- BEGIN checked continuation frames_chart_zero.lean -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.P1Charts
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LeBrunSalamon.P1Ideal

/-- The first-chart frame of the actual finite-point ideal has generator t-a. -/
def finitePointChartZeroData (a : ℂ) :
    IncludedFrame (pointIdealOnChart (pointMap 0 a) 0)
      (pointIdealChartInclusion (pointMap 0 a) 0)
      (affineScalarEnd (R := CommRingCat.of (Polynomial ℂ)) (finiteGeneratorZero a)) :=
  pointIdealChartIncludedFrameOfFactor (pointMap 0 a) 0
    (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)))
    (pointMap_eq_polynomialChart 0 a).symm (finiteGeneratorZero a)
    (affinePointFirstFrameData a)

/-- The first chart's actual normalized frame. -/
def finitePointChartZeroFrame (a : ℂ) :
    structureModule (Spec (CommRingCat.of (Polynomial ℂ))) ≅
      pointIdealOnChart (pointMap 0 a) 0 := (finitePointChartZeroData a).frame

@[reassoc]
theorem finitePointChartZeroFrame_hom_inclusion (a : ℂ) :
    (finitePointChartZeroFrame a).hom ≫ pointIdealChartInclusion (pointMap 0 a) 0 =
      affineScalarEnd (R := CommRingCat.of (Polynomial ℂ)) (finiteGeneratorZero a) :=
  (finitePointChartZeroData a).inclusion

end LeBrunSalamon.P1Ideal

end
/- END checked continuation frames_chart_zero.lean -/

/- BEGIN checked continuation frames_normalized.lean -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.P1Charts
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LeBrunSalamon.P1Ideal

theorem finitePoint_nonzero_second_factor (a : ℂ) (ha : a ≠ 0) :
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a⁻¹)) ≫
      polynomialChartInclusion 1 = pointMap 0 a :=
  (pointMap_eq_polynomialChart 1 a⁻¹).symm.trans (pointMap_zero_eq_one_inv a ha).symm

/-- The opposite polynomial chart misses a zero-coordinate point. -/
theorem coordinatePoint_complement_disjoint (i j : Fin 2) (hij : j ≠ i) :
    pointMap i 0 ⁻¹ᵁ (polynomialChartInclusion j).opensRange = ⊥ := by
  rw [polynomialChartInclusion_range, pointMap_preimage_chart, if_neg hij,
    PrimeSpectrum.basicOpen_zero]

theorem finitePoint_zero_second_disjoint (a : ℂ) (ha : a = 0) :
    pointMap 0 a ⁻¹ᵁ (polynomialChartInclusion 1).opensRange = ⊥ := by
  subst a
  exact coordinatePoint_complement_disjoint 0 1 (by decide)

/-- The second-chart generator is 1-a*s, also when this chart misses the point. -/
def finitePointChartOneData (a : ℂ) :
    IncludedFrame (pointIdealOnChart (pointMap 0 a) 1)
      (pointIdealChartInclusion (pointMap 0 a) 1)
      (affineScalarEnd (R := CommRingCat.of (Polynomial ℂ)) (finiteGeneratorOne a)) := by
  classical
  by_cases ha : a = 0
  · exact (pointIdealChartIncludedFrameOfDisjoint (pointMap 0 a) 1
      (finitePoint_zero_second_disjoint a ha)).congr
      (by simp only [ha, finiteGeneratorOne_zero, affineScalarEnd_one])
  · exact pointIdealChartIncludedFrameOfFactor (pointMap 0 a) 1
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a⁻¹)))
      (finitePoint_nonzero_second_factor a ha) (finiteGeneratorOne a)
      (affinePointSecondFrameData a ha)

def finitePointChartOneFrame (a : ℂ) :
    structureModule (Spec (CommRingCat.of (Polynomial ℂ))) ≅
      pointIdealOnChart (pointMap 0 a) 1 := (finitePointChartOneData a).frame

@[reassoc]
theorem finitePointChartOneFrame_hom_inclusion (a : ℂ) :
    (finitePointChartOneFrame a).hom ≫ pointIdealChartInclusion (pointMap 0 a) 1 =
      affineScalarEnd (R := CommRingCat.of (Polynomial ℂ)) (finiteGeneratorOne a) :=
  (finitePointChartOneData a).inclusion

/-- The first chart misses infinity, so its normalized generator is 1. -/
def infinityChartZeroData :
    IncludedFrame (pointIdealOnChart (pointMap 1 0) 0)
      (pointIdealChartInclusion (pointMap 1 0) 0)
      (𝟙 (structureModule (Spec (CommRingCat.of (Polynomial ℂ))))) :=
  pointIdealChartIncludedFrameOfDisjoint (pointMap 1 0) 0
    (coordinatePoint_complement_disjoint 1 0 (by decide))

/-- The actual second-chart kernel at infinity has normalized generator s. -/
def infinityChartOneData :
    IncludedFrame (pointIdealOnChart (pointMap 1 0) 1)
      (pointIdealChartInclusion (pointMap 1 0) 1)
      (affineScalarEnd (R := CommRingCat.of (Polynomial ℂ)) Polynomial.X) :=
  pointIdealChartIncludedFrameOfFactor (pointMap 1 0) 1
    (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : ℂ))))
    (pointMap_eq_polynomialChart 1 0).symm Polynomial.X affineInfinityFrameData

def infinityChartZeroFrame :
    structureModule (Spec (CommRingCat.of (Polynomial ℂ))) ≅
      pointIdealOnChart (pointMap 1 0) 0 := infinityChartZeroData.frame

def infinityChartOneFrame :
    structureModule (Spec (CommRingCat.of (Polynomial ℂ))) ≅
      pointIdealOnChart (pointMap 1 0) 1 := infinityChartOneData.frame

@[reassoc]
theorem infinityChartZeroFrame_hom_inclusion :
    infinityChartZeroFrame.hom ≫ pointIdealChartInclusion (pointMap 1 0) 0 = 𝟙 _ :=
  infinityChartZeroData.inclusion

@[reassoc]
theorem infinityChartOneFrame_hom_inclusion :
    infinityChartOneFrame.hom ≫ pointIdealChartInclusion (pointMap 1 0) 1 =
      affineScalarEnd (R := CommRingCat.of (Polynomial ℂ)) Polynomial.X :=
  infinityChartOneData.inclusion

/-- Every finite coordinate point has the specified normalized actual ideal frames. -/
def finitePointNormalizedFrames (a : ℂ) : NormalizedPointIdealFrames (pointMap 0 a) where
  generatorZero := finiteGeneratorZero a
  generatorOne := finiteGeneratorOne a
  generatorZero_ne_zero := finiteGeneratorZero_ne_zero a
  generatorOne_ne_zero := finiteGeneratorOne_ne_zero a
  frameZero := finitePointChartZeroFrame a
  frameOne := finitePointChartOneFrame a
  frameZero_inclusion := finitePointChartZeroFrame_hom_inclusion a
  frameOne_inclusion := finitePointChartOneFrame_hom_inclusion a
  overlap_transition := finiteGenerators_overlap_transition a

/-- The point at infinity has the same normalized overlap factor. -/
def infinityNormalizedFrames : NormalizedPointIdealFrames (pointMap 1 0) where
  generatorZero := 1
  generatorOne := Polynomial.X
  generatorZero_ne_zero := one_ne_zero
  generatorOne_ne_zero := Polynomial.X_ne_zero
  frameZero := infinityChartZeroFrame
  frameOne := infinityChartOneFrame
  frameZero_inclusion := by
    simpa only [affineScalarEnd_one] using infinityChartZeroFrame_hom_inclusion
  frameOne_inclusion := infinityChartOneFrame_hom_inclusion
  overlap_transition := infinityGenerators_overlap_transition

theorem canonicalPoint_normalizedFrames
    (p : Spec (CommRingCat.of ℂ) ⟶ lineScheme)
    (hp : p ≫ canonicalBaseMap = 𝟙 (Spec (CommRingCat.of ℂ))) :
    Nonempty (NormalizedPointIdealFrames p) := by
  rcases canonicalPoint_finite_or_infinity p hp with ⟨a, rfl⟩ | rfl
  · exact ⟨finitePointNormalizedFrames a⟩
  · exact ⟨infinityNormalizedFrames⟩

/-- A specified ideal isomorphism respecting its inclusion respects the chart inclusions. -/
@[reassoc]
theorem mapIso_pointIdealChartInclusion
    {p q : Spec (CommRingCat.of ℂ) ⟶ lineScheme}
    (e : kernel (structurePushforwardMap p) ≅ kernel (structurePushforwardMap q))
    (he : e.hom ≫ kernel.ι (structurePushforwardMap q) =
      kernel.ι (structurePushforwardMap p)) (i : Fin 2) :
    (Scheme.Modules.restrictFunctor (polynomialChartInclusion i)).map e.hom ≫
        pointIdealChartInclusion q i = pointIdealChartInclusion p i := by
  unfold pointIdealChartInclusion
  rw [← Category.assoc, ← Functor.map_comp, he]

/-- Normalize another presentation of the same embedded ideal through its actual inclusion. -/
def NormalizedPointIdealFrames.transport
    {p q : Spec (CommRingCat.of ℂ) ⟶ lineScheme}
    (d : NormalizedPointIdealFrames p)
    (e : kernel (structurePushforwardMap p) ≅ kernel (structurePushforwardMap q))
    (he : e.hom ≫ kernel.ι (structurePushforwardMap q) =
      kernel.ι (structurePushforwardMap p)) : NormalizedPointIdealFrames q where
  generatorZero := d.generatorZero
  generatorOne := d.generatorOne
  generatorZero_ne_zero := d.generatorZero_ne_zero
  generatorOne_ne_zero := d.generatorOne_ne_zero
  frameZero := d.frameZero ≪≫
    (Scheme.Modules.restrictFunctor (polynomialChartInclusion 0)).mapIso e
  frameOne := d.frameOne ≪≫
    (Scheme.Modules.restrictFunctor (polynomialChartInclusion 1)).mapIso e
  frameZero_inclusion := by
    rw [Iso.trans_hom, Functor.mapIso_hom, Category.assoc, mapIso_pointIdealChartInclusion e he]
    exact d.frameZero_inclusion
  frameOne_inclusion := by
    rw [Iso.trans_hom, Functor.mapIso_hom, Category.assoc, mapIso_pointIdealChartInclusion e he]
    exact d.frameOne_inclusion
  overlap_transition := d.overlap_transition

/-- The earlier source-isomorphism kernel comparison respects the actual ideal inclusion. -/
@[reassoc]
theorem structureKernel_precomposeIso_hom_ι {S T X : Scheme} (e : S ≅ T) (p : T ⟶ X) :
    (P1Restriction.structureKernel_precomposeIso e p).hom ≫
        kernel.ι (structurePushforwardMap p) =
      kernel.ι (structurePushforwardMap (e.hom ≫ p)) := by
  simp only [P1Restriction.structureKernel_precomposeIso, Iso.symm_hom,
    kernel.mapIso_inv, Iso.refl_inv, kernel.map, kernel.lift_ι, Category.comp_id]

/-- Reparameterizing Spec C preserves the normalized point-ideal frame certificate. -/
def normalizedFramesOfPrecomposeIso
    (e : Spec (CommRingCat.of ℂ) ≅ Spec (CommRingCat.of ℂ))
    (p : Spec (CommRingCat.of ℂ) ⟶ lineScheme)
    (d : NormalizedPointIdealFrames (e.hom ≫ p)) : NormalizedPointIdealFrames p :=
  d.transport (P1Restriction.structureKernel_precomposeIso e p)
    (structureKernel_precomposeIso_hom_ι e p)

/-- Every marked point for the existing complex-base identification admits
the normalized frames of its actual ideal sheaf. -/
theorem projectiveLinePoint_normalizedFrames
    (P : PhaseTwo.ProjectiveLineOverC) (p : PhaseTwo.ProjectiveLinePoint P) :
    Nonempty (NormalizedPointIdealFrames p.map) := by
  let q := PhaseTwo.ProjectiveLinePoint.rebase Skeleton.canonicalProjectiveLine p
  obtain ⟨d⟩ := canonicalPoint_normalizedFrames q.map q.overC
  exact ⟨normalizedFramesOfPrecomposeIso
    (Skeleton.canonicalProjectiveLine.zeroDegreeIso.symm ≪≫ P.zeroDegreeIso) p.map d⟩

end LeBrunSalamon.P1Ideal

end
/- END checked continuation frames_normalized.lean -/

/- BEGIN checked continuation overlap_base.lean -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.P1Charts
open scoped LaurentPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LeBrunSalamon.P1Ideal

theorem restrictedInclusion_mono {X Y : Scheme} (E : Y.Modules)
    (ι : E ⟶ SheafOfModules.unit Y.ringCatSheaf) [Mono ι]
    (f : X ⟶ Y) [IsOpenImmersion f] : Mono (restrictedInclusion E ι f) := by
  letI := restrict_preservesFiniteLimits f
  unfold restrictedInclusion
  infer_instance

theorem frame_transition_of_inclusions {C : Type*} [Category C]
    {O E A : C} (ι : E ⟶ A) [Mono ι] (e f : O ≅ E) (u : O ⟶ O)
    (g : O ⟶ A) (he : e.hom ≫ ι = g) (hf : f.hom ≫ ι = u ≫ g) :
    f.hom = u ≫ e.hom := by
  apply (cancel_mono ι).1
  rw [hf, Category.assoc, he]

theorem frame_comparisons_of_common_transition {C : Type*} [Category C]
    {O E F : C} (e₀ e₁ : O ≅ E) (f₀ f₁ : O ≅ F) (u : O ≅ O)
    (he : e₁ = u ≪≫ e₀) (hf : f₁ = u ≪≫ f₀) :
    e₀.symm ≪≫ f₀ = e₁.symm ≪≫ f₁ := by
  rw [he, hf]
  apply Iso.ext
  simp

theorem NormalizedPointIdealFrames.laurent_transition
    {p : Spec (CommRingCat.of ℂ) ⟶ lineScheme} (d : NormalizedPointIdealFrames p) :
    LaurentPolynomial.invert d.generatorOne.toLaurent =
      LaurentPolynomial.T (-1) * d.generatorZero.toLaurent := by
  have h := congrArg overlapRingEquiv d.overlap_transition
  rw [map_mul, overlapRingEquiv_chartOne, overlapRingEquiv_ratioOne,
    overlapRingEquiv_chartZero] at h
  change LaurentPolynomial.invert
      (chartRingEquiv 1 ((chartRingEquiv 1).symm d.generatorOne)).toLaurent =
    LaurentPolynomial.T (-1) *
      (chartRingEquiv 0 ((chartRingEquiv 0).symm d.generatorZero)).toLaurent at h
  simpa only [RingEquiv.apply_symm_apply] using h

def idealLaurentTransitionUnit : ℂ[T;T⁻¹]ˣ where
  val := LaurentPolynomial.T (-1)
  inv := LaurentPolynomial.T 1
  val_inv := by rw [← LaurentPolynomial.T_add]; norm_num
  inv_val := by rw [← LaurentPolynomial.T_add]; norm_num

end LeBrunSalamon.P1Ideal


end
/- END checked continuation overlap_base.lean -/

/- BEGIN checked continuation overlap_objects.lean -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.P1Charts
open scoped LaurentPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LeBrunSalamon.P1Ideal

abbrev pointIdealOnOverlap (p : Spec (CommRingCat.of ℂ) ⟶ lineScheme) :
    (Spec (CommRingCat.of ℂ[T;T⁻¹])).Modules :=
  (kernel (structurePushforwardMap p)).restrict
    (polynomialOverlapToZero ≫ polynomialChartInclusion 0)

def pointIdealOverlapInclusion (p : Spec (CommRingCat.of ℂ) ⟶ lineScheme) :
    pointIdealOnOverlap p ⟶ affineStructureModule (CommRingCat.of ℂ[T;T⁻¹]) :=
  restrictedInclusion (kernel (structurePushforwardMap p))
    (kernel.ι (structurePushforwardMap p))
    (polynomialOverlapToZero ≫ polynomialChartInclusion 0)

instance pointIdealOverlapInclusion_mono
    (p : Spec (CommRingCat.of ℂ) ⟶ lineScheme) :
    Mono (pointIdealOverlapInclusion p) := by
  exact restrictedInclusion_mono (kernel (structurePushforwardMap p))
    (kernel.ι (structurePushforwardMap p))
    (polynomialOverlapToZero ≫ polynomialChartInclusion 0)

def pointIdealOverlapZeroFrame
    {p : Spec (CommRingCat.of ℂ) ⟶ lineScheme} (d : NormalizedPointIdealFrames p) :
    affineStructureModule (CommRingCat.of ℂ[T;T⁻¹]) ≅ pointIdealOnOverlap p :=
  restrictedFrame (kernel (structurePushforwardMap p))
    polynomialOverlapToZero (polynomialChartInclusion 0) d.frameZero

def pointIdealOverlapOneFrame
    {p : Spec (CommRingCat.of ℂ) ⟶ lineScheme} (d : NormalizedPointIdealFrames p) :
    affineStructureModule (CommRingCat.of ℂ[T;T⁻¹]) ≅ pointIdealOnOverlap p :=
  restrictedFrame (kernel (structurePushforwardMap p))
      polynomialOverlapToOne (polynomialChartInclusion 1) d.frameOne ≪≫
    (Scheme.Modules.restrictFunctorCongr polynomialOverlap_condition.symm).app
      (kernel (structurePushforwardMap p))

end LeBrunSalamon.P1Ideal


end
/- END checked continuation overlap_objects.lean -/

/- BEGIN checked continuation overlap_affine_transport.lean -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwentyFive

namespace LeBrunSalamon.P1Ideal

/-- Restrict a local frame, then transport it along a specified equality of
open immersions. All scheme parameters stay symbolic in this construction. -/
def transportedRestrictedFrame {X Y Z : Scheme} (E : Z.Modules)
    (f : X ⟶ Y) (j : Y ⟶ Z) (k : X ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion j] [IsOpenImmersion k]
    (h : f ≫ j = k)
    (e : SheafOfModules.unit Y.ringCatSheaf ≅ E.restrict j) :
    SheafOfModules.unit X.ringCatSheaf ≅ E.restrict k :=
  restrictedFrame (X := X) (Y := Y) (Z := Z) E f j e ≪≫
    (Scheme.Modules.restrictFunctorCongr
      (X := X) (Y := Z) (f := f ≫ j) (g := k) h).app E

/-- A normalized affine inclusion survives the generic transported-frame
construction, without unfolding any concrete projective chart. -/
@[reassoc]
theorem transportedRestrictedFrame_affine_hom_inclusion
    {R S : CommRingCat} {Z : Scheme}
    (E : Z.Modules) (ι : E ⟶ SheafOfModules.unit Z.ringCatSheaf)
    (φ : R ⟶ S) [IsOpenImmersion (Spec.map φ)]
    (j : Spec R ⟶ Z) [IsOpenImmersion j]
    (k : Spec S ⟶ Z) [IsOpenImmersion k]
    (h : Spec.map φ ≫ j = k)
    (e : affineStructureModule R ≅ E.restrict j) (r : R)
    (he : e.hom ≫ restrictedInclusion (X := Spec R) (Y := Z) E ι j =
      affineScalarEnd (R := R) r) :
    (transportedRestrictedFrame (X := Spec S) (Y := Spec R) (Z := Z)
      E (Spec.map φ) j k h e).hom ≫
        restrictedInclusion (X := Spec S) (Y := Z) E ι k =
      affineScalarEnd (R := S) (φ r) := by
  rw [transportedRestrictedFrame, Iso.trans_hom, Category.assoc]
  change (restrictedFrame (X := Spec S) (Y := Spec R) (Z := Z)
      E (Spec.map φ) j e).hom ≫
    (Scheme.Modules.restrictFunctorCongr (X := Spec S) (Y := Z)
      (f := Spec.map φ ≫ j) (g := k) h).hom.app E ≫
        restrictedInclusion (X := Spec S) (Y := Z) E ι k =
      affineScalarEnd (R := S) (φ r)
  rw [restrictedInclusion_congr (X := Spec S) (Y := Z) E ι h]
  exact restrictedFrame_affine_hom_inclusion (R := R) (S := S) (Z := Z)
    E ι φ j e r he

end LeBrunSalamon.P1Ideal


end
/- END checked continuation overlap_affine_transport.lean -/

/- BEGIN checked continuation overlap_frames.lean -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.P1Charts
open scoped LaurentPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LeBrunSalamon.P1Ideal

/-- The first actual overlap frame has the image of its polynomial generator. -/
@[reassoc]
theorem pointIdealOverlapZeroFrame_hom_inclusion
    {p : Spec (CommRingCat.of ℂ) ⟶ lineScheme} (d : NormalizedPointIdealFrames p) :
    (pointIdealOverlapZeroFrame d).hom ≫ pointIdealOverlapInclusion p =
      affineScalarEnd d.generatorZero.toLaurent := by
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Polynomial.toLaurent : Polynomial ℂ →+* ℂ[T;T⁻¹]))) :=
    polynomialOverlapToZero_isOpenImmersion
  exact restrictedFrame_affine_hom_inclusion
    (R := CommRingCat.of (Polynomial ℂ)) (S := CommRingCat.of ℂ[T;T⁻¹])
    (Z := lineScheme)
    (kernel (structurePushforwardMap p)) (kernel.ι (structurePushforwardMap p))
    (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial ℂ →+* ℂ[T;T⁻¹]))
    (polynomialChartInclusion 0) d.frameZero d.generatorZero d.frameZero_inclusion


/-- The second actual frame has the generator after inversion of the Laurent coordinate. -/
@[reassoc]
theorem pointIdealOverlapOneFrame_hom_inclusion
    {p : Spec (CommRingCat.of ℂ) ⟶ lineScheme} (d : NormalizedPointIdealFrames p) :
    (pointIdealOverlapOneFrame d).hom ≫ pointIdealOverlapInclusion p =
      affineScalarEnd (LaurentPolynomial.invert d.generatorOne.toLaurent) := by
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (LaurentPolynomial.invert.toRingHom.comp
        (Polynomial.toLaurent : Polynomial ℂ →+* ℂ[T;T⁻¹])))) :=
    polynomialOverlapToOne_isOpenImmersion
  exact transportedRestrictedFrame_affine_hom_inclusion
    (R := CommRingCat.of (Polynomial ℂ)) (S := CommRingCat.of ℂ[T;T⁻¹])
    (Z := lineScheme)
    (kernel (structurePushforwardMap p)) (kernel.ι (structurePushforwardMap p))
    (CommRingCat.ofHom
      (LaurentPolynomial.invert.toRingHom.comp
        (Polynomial.toLaurent : Polynomial ℂ →+* ℂ[T;T⁻¹])))
    (polynomialChartInclusion 1)
    (polynomialOverlapToZero ≫ polynomialChartInclusion 0)
    polynomialOverlap_condition.symm d.frameOne d.generatorOne d.frameOne_inclusion


/-- The actual ideal frames have the common invertible transition t⁻¹. -/
theorem pointIdealOverlapFrame_transition
    {p : Spec (CommRingCat.of ℂ) ⟶ lineScheme} (d : NormalizedPointIdealFrames p) :
    (pointIdealOverlapOneFrame d).hom =
      affineScalarEnd (LaurentPolynomial.T (-1) : ℂ[T;T⁻¹]) ≫
        (pointIdealOverlapZeroFrame d).hom := by
  apply frame_transition_of_inclusions (pointIdealOverlapInclusion p)
    (pointIdealOverlapZeroFrame d) (pointIdealOverlapOneFrame d)
    (affineScalarEnd (LaurentPolynomial.T (-1) : ℂ[T;T⁻¹]))
    (affineScalarEnd d.generatorZero.toLaurent)
    (pointIdealOverlapZeroFrame_hom_inclusion d)
  rw [pointIdealOverlapOneFrame_hom_inclusion, affineScalarEnd_comp,
    d.laurent_transition]


/-- The transition equation as an equality of frame isomorphisms. -/
theorem pointIdealOverlapFrame_iso_transition
    {p : Spec (CommRingCat.of ℂ) ⟶ lineScheme} (d : NormalizedPointIdealFrames p) :
    pointIdealOverlapOneFrame d =
      affineScalarIso idealLaurentTransitionUnit ≪≫ pointIdealOverlapZeroFrame d := by
  apply Iso.ext
  exact pointIdealOverlapFrame_transition d


/-- Normalized comparisons of any two actual point ideals agree on the overlap. -/
theorem pointIdealOverlapComparison_independent
    {p q : Spec (CommRingCat.of ℂ) ⟶ lineScheme}
    (d : NormalizedPointIdealFrames p) (e : NormalizedPointIdealFrames q) :
    (pointIdealOverlapZeroFrame d).symm ≪≫ pointIdealOverlapZeroFrame e =
      (pointIdealOverlapOneFrame d).symm ≪≫ pointIdealOverlapOneFrame e := by
  exact frame_comparisons_of_common_transition
    (pointIdealOverlapZeroFrame d) (pointIdealOverlapOneFrame d)
    (pointIdealOverlapZeroFrame e) (pointIdealOverlapOneFrame e)
    (affineScalarIso idealLaurentTransitionUnit)
    (pointIdealOverlapFrame_iso_transition d) (pointIdealOverlapFrame_iso_transition e)


end LeBrunSalamon.P1Ideal


end
/- END checked continuation overlap_frames.lean -/

/- BEGIN checked continuation glue_restriction.lean -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite
namespace LeBrunSalamon.ModuleGluing

/-- Restriction along a genuine scheme isomorphism is an equivalence of module categories. -/
def restrictEquivalence {X Y : Scheme} (e : X ≅ Y) : Y.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.restrictFunctor e.hom)
    (Scheme.Modules.restrictFunctor e.inv)
    ((Scheme.Modules.restrictFunctorId (X := Y)).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr e.inv_hom_id).symm ≪≫
        Scheme.Modules.restrictFunctorComp e.inv e.hom)
    ((Scheme.Modules.restrictFunctorComp e.hom e.inv).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.hom_inv_id ≪≫
        Scheme.Modules.restrictFunctorId)

@[simp]
theorem restrict_map_app {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    {E F : Y.Modules} (a : E ⟶ F) (W : X.Opens) :
    ((Scheme.Modules.restrictFunctor f).map a).app W = a.app (f ''ᵁ W) := rfl

/-- Restrict a local isomorphism along another open immersion, retaining the canonical comparison. -/
def restrictLocalIso {X U V : Scheme} {E F : X.Modules}
    (f : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion f] [IsOpenImmersion j]
    (e : E.restrict j ≅ F.restrict j) :
    E.restrict (f ≫ j) ≅ F.restrict (f ≫ j) :=
  (Scheme.Modules.restrictFunctorComp f j).app E ≪≫
    (Scheme.Modules.restrictFunctor f).mapIso e ≪≫
      ((Scheme.Modules.restrictFunctorComp f j).app F).symm

/-- Move a local isomorphism between equal presentations of its open immersion. -/
def transportRestrictIso {X U : Scheme} {E F : X.Modules}
    {i j : U ⟶ X} [IsOpenImmersion i] [IsOpenImmersion j]
    (h : i = j) (e : E.restrict i ≅ F.restrict i) : E.restrict j ≅ F.restrict j :=
  ((Scheme.Modules.restrictFunctorCongr h).app E).symm ≪≫ e ≪≫
    (Scheme.Modules.restrictFunctorCongr h).app F

@[simp]
theorem restrictFunctorCongr_rfl {X U : Scheme} (i : U ⟶ X) [IsOpenImmersion i] :
    Scheme.Modules.restrictFunctorCongr (rfl : i = i) = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext E
  apply Scheme.Modules.hom_ext
  intro W
  simp only [Scheme.Modules.restrictFunctorCongr_hom_app_app,
    Iso.refl_hom, NatTrans.id_app, Scheme.Modules.Hom.id_app]
  change E.presheaf.map (𝟙 _) = 𝟙 _
  exact E.presheaf.map_id _

@[simp]
theorem transportRestrictIso_rfl {X U : Scheme} {E F : X.Modules}
    (i : U ⟶ X) [IsOpenImmersion i] (e : E.restrict i ≅ F.restrict i) :
    transportRestrictIso (rfl : i = i) e = e := by
  apply Iso.ext
  simp only [transportRestrictIso, restrictFunctorCongr_rfl, Iso.trans_hom,
    Iso.symm_hom, Iso.app_hom, Iso.app_inv, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Category.id_comp, Category.comp_id]

/-- Restriction-composition comparisons satisfy associativity on actual module sheaves. -/
theorem restrictionComp_coherence {X A B C : Scheme} (E : X.Modules)
    (g : C ⟶ B) (f : B ⟶ A) (j : A ⟶ X)
    [IsOpenImmersion g] [IsOpenImmersion f] [IsOpenImmersion j] :
    (Scheme.Modules.restrictFunctorCongr (Category.assoc g f j)).hom.app E ≫
      (Scheme.Modules.restrictFunctorComp g (f ≫ j)).hom.app E ≫
        (Scheme.Modules.restrictFunctor g).map
          ((Scheme.Modules.restrictFunctorComp f j).hom.app E) =
      (Scheme.Modules.restrictFunctorComp (g ≫ f) j).hom.app E ≫
        (Scheme.Modules.restrictFunctorComp g f).hom.app (E.restrict j) := by
  apply Scheme.Modules.hom_ext
  intro W
  simp only [Scheme.Modules.Hom.comp_app,
    Scheme.Modules.restrictFunctorCongr_hom_app_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app, restrict_map_app,
    Scheme.Modules.restrict_map, ← Functor.map_comp]
  congr 1

/-- Successive local restriction agrees with direct restriction, up to the specified associativity. -/
theorem restrictLocalIso_comp {X A B C : Scheme} {E F : X.Modules}
    (g : C ⟶ B) (f : B ⟶ A) (j : A ⟶ X)
    [IsOpenImmersion g] [IsOpenImmersion f] [IsOpenImmersion j]
    (e : E.restrict j ≅ F.restrict j) :
    transportRestrictIso (Category.assoc g f j) (restrictLocalIso (g ≫ f) j e) =
      restrictLocalIso g (f ≫ j) (restrictLocalIso f j e) := by
  have hE := restrictionComp_coherence E g f j
  have hF := restrictionComp_coherence F g f j
  have hn := (Scheme.Modules.restrictFunctorComp g f).hom.naturality e.hom
  apply Iso.ext
  simp only [transportRestrictIso, restrictLocalIso, Iso.trans_hom,
    Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc]
  apply (cancel_epi ((Scheme.Modules.restrictFunctorCongr
    (Category.assoc g f j)).hom.app E)).1
  apply (cancel_mono ((Scheme.Modules.restrictFunctorComp g (f ≫ j)).hom.app F ≫
    (Scheme.Modules.restrictFunctor g).map
      ((Scheme.Modules.restrictFunctorComp f j).hom.app F))).1
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app] at *
  rw [hF]
  simp only [Iso.inv_hom_id_app_assoc, Functor.map_comp]
  rw [(Scheme.Modules.restrictFunctor g).map_id
    ((Scheme.Modules.restrictFunctor j ⋙ Scheme.Modules.restrictFunctor f).obj F)]
  simp only [Functor.comp_obj, Scheme.Modules.restrict, Category.comp_id]
  have hE' := congrArg (fun a => a ≫
    (Scheme.Modules.restrictFunctor g).map
      ((Scheme.Modules.restrictFunctor f).map e.hom)) hE
  simp only [Category.assoc] at hE'
  rw [hE']
  simpa only [Category.assoc, Functor.comp_map, Functor.comp_obj,
    Scheme.Modules.restrict] using congrArg
    (fun a => (Scheme.Modules.restrictFunctorComp (g ≫ f) j).hom.app E ≫ a) hn

/-- Restrict a local isomorphism and identify the resulting immersion with a specified one. -/
def restrictIsoAlong {X U V : Scheme} {E F : X.Modules}
    (f : V ⟶ U) (j : U ⟶ X) (i : V ⟶ X)
    [IsOpenImmersion f] [IsOpenImmersion j] [IsOpenImmersion i]
    (h : f ≫ j = i) (e : E.restrict j ≅ F.restrict j) : E.restrict i ≅ F.restrict i :=
  transportRestrictIso h (restrictLocalIso f j e)

/-- The specified-immersion restriction is functorial under composition. -/
theorem restrictIsoAlong_comp {X A B C : Scheme} {E F : X.Modules}
    (f : B ⟶ A) (j : A ⟶ X) (i : B ⟶ X)
    (g : C ⟶ B) (k : C ⟶ X)
    [IsOpenImmersion f] [IsOpenImmersion j] [IsOpenImmersion i]
    [IsOpenImmersion g] [IsOpenImmersion k]
    (h : f ≫ j = i) (h' : g ≫ i = k) (e : E.restrict j ≅ F.restrict j) :
    restrictIsoAlong g i k h' (restrictIsoAlong f j i h e) =
      restrictIsoAlong (g ≫ f) j k (by rw [Category.assoc, h, h']) e := by
  subst i
  subst k
  simpa only [restrictIsoAlong, transportRestrictIso_rfl] using
    (restrictLocalIso_comp g f j e).symm

/-- Restriction along a scheme isomorphism detects equality of local isomorphisms. -/
theorem restrictIsoAlong_injective {X U V : Scheme} {E F : X.Modules}
    (c : V ≅ U) (j : U ⟶ X) (i : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion i] (h : c.hom ≫ j = i) :
    Function.Injective (restrictIsoAlong (E := E) (F := F) c.hom j i h) := by
  intro e e' he
  let R := (restrictEquivalence c).functor
  apply R.mapIso_injective
  apply Iso.ext
  dsimp only [R, restrictEquivalence, CategoryTheory.Equivalence.mk]
  have hh := congrArg (fun a =>
    ((Scheme.Modules.restrictFunctorComp c.hom j).app E).inv ≫
      ((Scheme.Modules.restrictFunctorCongr h).app E).hom ≫ a.hom ≫
      ((Scheme.Modules.restrictFunctorCongr h).app F).inv ≫
      ((Scheme.Modules.restrictFunctorComp c.hom j).app F).hom) he
  simpa [restrictIsoAlong, transportRestrictIso, restrictLocalIso, Category.assoc] using hh


end LeBrunSalamon.ModuleGluing

end
/- END checked continuation glue_restriction.lean -/

/- BEGIN checked continuation point_frame_comparison.lean -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.ModuleGluing

namespace LeBrunSalamon.P1Ideal

/-- The unit comparison cancels when two actual restricted frames are compared. -/
theorem restrictedFrame_comparison {X Y Z : Scheme} {E F : Z.Modules}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g]
    (e : SheafOfModules.unit Y.ringCatSheaf ≅ E.restrict g)
    (e' : SheafOfModules.unit Y.ringCatSheaf ≅ F.restrict g) :
    (restrictedFrame E f g e).symm ≪≫ restrictedFrame F f g e' =
      restrictLocalIso f g (e.symm ≪≫ e') := by
  apply Iso.ext
  simp [restrictedFrame, restrictLocalIso, Functor.map_comp, Category.assoc]

/-- Comparing transported frames agrees with transporting the actual comparison. -/
theorem transportedFrame_comparison {X Y : Scheme} {E F : Y.Modules}
    {f g : X ⟶ Y} [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g)
    (e : SheafOfModules.unit X.ringCatSheaf ≅ E.restrict f)
    (e' : SheafOfModules.unit X.ringCatSheaf ≅ F.restrict f) :
    (e ≪≫ (Scheme.Modules.restrictFunctorCongr h).app E).symm ≪≫
        (e' ≪≫ (Scheme.Modules.restrictFunctorCongr h).app F) =
      transportRestrictIso h (e.symm ≪≫ e') := by
  apply Iso.ext
  simp [transportRestrictIso, Category.assoc]

open LeBrunSalamon.P1Charts

/-- The first actual Laurent frame comparison is the restriction of the first chart comparison. -/
theorem pointIdealOverlapZeroFrame_comparison
    {p q : Spec (CommRingCat.of ℂ) ⟶ lineScheme}
    (d : NormalizedPointIdealFrames p) (e : NormalizedPointIdealFrames q) :
    (pointIdealOverlapZeroFrame d).symm ≪≫ pointIdealOverlapZeroFrame e =
      restrictLocalIso polynomialOverlapToZero (polynomialChartInclusion 0)
        (d.frameZero.symm ≪≫ e.frameZero) :=
  restrictedFrame_comparison polynomialOverlapToZero (polynomialChartInclusion 0)
    d.frameZero e.frameZero

/-- The second actual Laurent comparison has the prescribed equal-composite transport. -/
theorem pointIdealOverlapOneFrame_comparison
    {p q : Spec (CommRingCat.of ℂ) ⟶ lineScheme}
    (d : NormalizedPointIdealFrames p) (e : NormalizedPointIdealFrames q) :
    (pointIdealOverlapOneFrame d).symm ≪≫ pointIdealOverlapOneFrame e =
      transportRestrictIso polynomialOverlap_condition.symm
        (restrictLocalIso polynomialOverlapToOne (polynomialChartInclusion 1)
          (d.frameOne.symm ≪≫ e.frameOne)) := by
  change ((restrictedFrame (kernel (structurePushforwardMap p))
      polynomialOverlapToOne (polynomialChartInclusion 1) d.frameOne) ≪≫
      (Scheme.Modules.restrictFunctorCongr polynomialOverlap_condition.symm).app
        (kernel (structurePushforwardMap p))).symm ≪≫
    ((restrictedFrame (kernel (structurePushforwardMap q))
      polynomialOverlapToOne (polynomialChartInclusion 1) e.frameOne) ≪≫
      (Scheme.Modules.restrictFunctorCongr polynomialOverlap_condition.symm).app
        (kernel (structurePushforwardMap q))) = _
  rw [transportedFrame_comparison, restrictedFrame_comparison]

/-- The normalized actual chart comparisons satisfy the genuine sheaf overlap condition. -/
theorem pointIdealChartComparison_compatible
    {p q : Spec (CommRingCat.of ℂ) ⟶ lineScheme}
    (d : NormalizedPointIdealFrames p) (e : NormalizedPointIdealFrames q) :
    restrictLocalIso polynomialOverlapToZero (polynomialChartInclusion 0)
        (d.frameZero.symm ≪≫ e.frameZero) =
      transportRestrictIso polynomialOverlap_condition.symm
        (restrictLocalIso polynomialOverlapToOne (polynomialChartInclusion 1)
          (d.frameOne.symm ≪≫ e.frameOne)) := by
  rw [← pointIdealOverlapZeroFrame_comparison, ← pointIdealOverlapOneFrame_comparison]
  exact pointIdealOverlapComparison_independent d e

end LeBrunSalamon.P1Ideal


end
/- END checked continuation point_frame_comparison.lean -/

/- BEGIN checked continuation glue_site_apps.lean -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
universe u
namespace LeBrunSalamon.ModuleGluing

/-- The two maps of open categories underlying restriction through an over site agree. -/
def overMapOpensComparison {X : Scheme.{u}} {U V : X.Opens} (i : V ⟶ U) :
    (X.homOfLE (leOfHom i)).opensFunctor ⋙ U.overEquivalence.symm.functor ≅
      V.overEquivalence.symm.functor ⋙ Over.map i := by
  refine NatIso.ofComponents (fun W ↦ Over.isoMk (eqToIso ?_) ?_) ?_
  · suffices U.ι ''ᵁ ((X.homOfLE (leOfHom i)) ''ᵁ W) = V.ι ''ᵁ W by simpa
    simp [← Scheme.Hom.comp_image]
  · cat_disch
  · cat_disch

set_option maxHeartbeats 800000 in
set_option backward.defeqAttrib.useBackward true in
/-- App-level comparison, first stated for an arbitrary module on the over site. -/
@[simp]
theorem overMapComparison_hom_app {X : Scheme.{u}} {U V : X.Opens}
    (i : V ⟶ U) (M : SheafOfModules.{u} (X.ringCatSheaf.over U))
    (W : V.toScheme.Opens) :
    ((Scheme.Modules.overMapCompOverEquiv i).hom.app M).app W =
      M.val.presheaf.map ((overMapOpensComparison i).hom.app W).op := rfl

end LeBrunSalamon.ModuleGluing

end
/- END checked continuation glue_site_apps.lean -/

/- BEGIN checked continuation glue_scheme_opens.lean -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.P1Ideal

namespace LeBrunSalamon.ModuleGluing

/-- Compare restriction to a smaller open with iterated restriction to that open. -/
def subopenComparison {X : Scheme} (E : X.Modules) {U V : X.Opens} (i : V ⟶ U) :
    E.restrict V.ι ≅ (E.restrict U.ι).restrict (X.homOfLE (leOfHom i)) :=
  ((Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι (leOfHom i))).app E).symm ≪≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE (leOfHom i)) U.ι).app E

/-- Restrict an actual open-subscheme module isomorphism using canonical comparisons. -/
def restrictOpenIso {X : Scheme} {E F : X.Modules} {U V : X.Opens} (i : V ⟶ U)
    (e : E.restrict U.ι ≅ F.restrict U.ι) : E.restrict V.ι ≅ F.restrict V.ι :=
  subopenComparison E i ≪≫
    (Scheme.Modules.restrictFunctor (X.homOfLE (leOfHom i))).mapIso e ≪≫
      (subopenComparison F i).symm

/-- Interpret an actual open-subscheme isomorphism in the corresponding over site. -/
def overIsoOfOpenIso {X : Scheme} {E F : X.Modules} (U : X.Opens)
    (e : E.restrict U.ι ≅ F.restrict U.ι) : E.over U ≅ F.over U :=
  (Scheme.Modules.overEquiv U).functor.preimageIso
    ((Scheme.Modules.overFunctorEquiv U).app E ≪≫ e ≪≫
      ((Scheme.Modules.overFunctorEquiv U).app F).symm)

@[simp]
theorem map_overIsoOfOpenIso {X : Scheme} {E F : X.Modules} (U : X.Opens)
    (e : E.restrict U.ι ≅ F.restrict U.ι) :
    (Scheme.Modules.overEquiv U).functor.mapIso (overIsoOfOpenIso U e) =
      (Scheme.Modules.overFunctorEquiv U).app E ≪≫ e ≪≫
        ((Scheme.Modules.overFunctorEquiv U).app F).symm := by
  apply Iso.ext
  simp [overIsoOfOpenIso]

@[simp]
theorem overFunctorEquiv_hom_app {X : Scheme} (E : X.Modules) (U : X.Opens)
    (W : U.toScheme.Opens) :
    ((Scheme.Modules.overFunctorEquiv U).hom.app E).app W = 𝟙 _ := rfl

@[simp]
theorem overFunctorEquiv_inv_app {X : Scheme} (E : X.Modules) (U : X.Opens)
    (W : U.toScheme.Opens) :
    ((Scheme.Modules.overFunctorEquiv U).inv.app E).app W = 𝟙 _ := rfl

@[simp]
theorem overFunctorMap_inv_app {X : Scheme} (E : X.Modules) {U V : X.Opens}
    (i : V ⟶ U) (W : V.toScheme.Opens) :
    ((Scheme.Modules.overEquiv V).functor.map
      ((SheafOfModules.overFunctorMap X.ringCatSheaf i).inv.app E)).app W = 𝟙 _ := rfl

set_option maxHeartbeats 800000 in
set_option backward.defeqAttrib.useBackward true in
/-- The two canonical ways of comparing a restricted over site with a smaller open agree. -/
theorem overRestriction_coherence {X : Scheme} (E : X.Modules) {U V : X.Opens}
    (i : V ⟶ U) :
    (Scheme.Modules.overEquiv V).functor.mapIso
        (((SheafOfModules.overFunctorMap X.ringCatSheaf i).app E).symm) ≪≫
      (Scheme.Modules.overMapCompOverEquiv i).app (E.over U) ≪≫
        (Scheme.Modules.restrictFunctor (X.homOfLE (leOfHom i))).mapIso
          ((Scheme.Modules.overFunctorEquiv U).app E) =
      (Scheme.Modules.overFunctorEquiv V).app E ≪≫ subopenComparison E i := by
  apply Iso.ext
  apply Scheme.Modules.hom_ext
  intro W
  apply AddCommGrpCat.ext
  intro x
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.app_inv, Scheme.Modules.Hom.comp_app, overFunctorMap_inv_app,
    overMapComparison_hom_app, restrict_map_app, overFunctorEquiv_hom_app,
    Category.id_comp, Category.comp_id, Functor.comp_obj, subopenComparison,
    Scheme.Modules.restrictFunctorCongr_inv_app_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app, ← Functor.map_comp,
    AddCommGrpCat.comp_apply, AddCommGrpCat.id_apply]
  change E.presheaf.map _ x = E.presheaf.map _ x
  exact congrArg (fun f => E.presheaf.map f x) (Subsingleton.elim _ _)

/-- Converting local isomorphisms to over sites commutes with actual open restriction. -/
theorem overIsoOfOpenIso_restrict {X : Scheme} {E F : X.Modules} {U V : X.Opens}
    (i : V ⟶ U) (e : E.restrict U.ι ≅ F.restrict U.ι) :
    restrictOverIso i (overIsoOfOpenIso U e) =
      overIsoOfOpenIso V (restrictOpenIso i e) := by
  let A := (Scheme.Modules.overEquiv V).functor
  let B := (Scheme.Modules.overEquiv U).functor
  let T := Scheme.Modules.restrictFunctor (X.homOfLE (leOfHom i))
  let s := overIsoOfOpenIso U e
  let dE := ((SheafOfModules.overFunctorMap X.ringCatSheaf i).app E).symm
  let dF := ((SheafOfModules.overFunctorMap X.ringCatSheaf i).app F).symm
  let bE := (Scheme.Modules.overMapCompOverEquiv i).app (E.over U)
  let bF := (Scheme.Modules.overMapCompOverEquiv i).app (F.over U)
  let aE := (Scheme.Modules.overFunctorEquiv U).app E
  let aF := (Scheme.Modules.overFunctorEquiv U).app F
  have hn : A.mapIso ((SheafOfModules.overMap X.ringCatSheaf i).mapIso s) =
      bE ≪≫ T.mapIso (B.mapIso s) ≪≫ bF.symm := by
    apply Iso.ext
    exact (NatIso.naturality_2 (Scheme.Modules.overMapCompOverEquiv i) s.hom).symm
  have hm : A.mapIso (restrictOverIso i s) =
      A.mapIso (overIsoOfOpenIso V (restrictOpenIso i e)) := by
    calc
      _ = (A.mapIso dE ≪≫ bE ≪≫ T.mapIso aE) ≪≫ T.mapIso e ≪≫
          (A.mapIso dF ≪≫ bF ≪≫ T.mapIso aF).symm := by
        simp only [restrictOverIso, Functor.mapIso_trans, hn, s,
          map_overIsoOfOpenIso, Functor.mapIso_symm]
        apply Iso.ext
        simp [dE, dF, aE, aF, bE, bF, A, B, T, Category.assoc]
      _ = ((Scheme.Modules.overFunctorEquiv V).app E ≪≫ subopenComparison E i) ≪≫
          T.mapIso e ≪≫
          ((Scheme.Modules.overFunctorEquiv V).app F ≪≫ subopenComparison F i).symm := by
        rw [overRestriction_coherence, overRestriction_coherence]
      _ = _ := by
        rw [map_overIsoOfOpenIso]
        apply Iso.ext
        simp [restrictOpenIso, T, Category.assoc]
  apply Iso.ext
  exact A.map_injective (congrArg Iso.hom hm)

/-- Compatible isomorphisms on actual open subschemes glue to a global module isomorphism. -/
def glueOpenIso {X : Scheme} {E F : X.Modules} {I : Type}
    (U : I → X.Opens) (hcover : iSup U = ⊤)
    (e : ∀ i, E.restrict (U i).ι ≅ F.restrict (U i).ι)
    (h : ∀ i j,
      restrictOpenIso (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) (e i) =
        restrictOpenIso (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)) (e j)) : E ≅ F :=
  glueOverIso U hcover (fun i => overIsoOfOpenIso (U i) (e i)) (by
    intro i j
    rw [overIsoOfOpenIso_restrict, overIsoOfOpenIso_restrict, h i j])

/-- Transfer a local isomorphism along a specified geometric chart comparison. -/
def chartComparisonIso {X U V : Scheme} {E F : X.Modules}
    (i : U ⟶ X) (j : V ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j]
    (c : U ≅ V) (hc : c.hom ≫ j = i)
    (e : E.restrict j ≅ F.restrict j) : E.restrict i ≅ F.restrict i :=
  ((Scheme.Modules.restrictFunctorCongr hc).app E).symm ≪≫
    (Scheme.Modules.restrictFunctorComp c.hom j).app E ≪≫
      (Scheme.Modules.restrictFunctor c.hom).mapIso e ≪≫
        ((Scheme.Modules.restrictFunctorComp c.hom j).app F).symm ≪≫
          (Scheme.Modules.restrictFunctorCongr hc).app F


end LeBrunSalamon.ModuleGluing

end
/- END checked continuation glue_scheme_opens.lean -/

/- BEGIN checked continuation glue_chart_iso.lean -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.P1Ideal

namespace LeBrunSalamon.ModuleGluing

theorem restrictOpenIso_eq_along {X : Scheme} {E F : X.Modules} {U V : X.Opens}
    (i : V ⟶ U) (e : E.restrict U.ι ≅ F.restrict U.ι) :
    restrictOpenIso i e = restrictIsoAlong (X.homOfLE (leOfHom i)) U.ι V.ι
      (X.homOfLE_ι (leOfHom i)) e := by
  apply Iso.ext
  simp [restrictOpenIso, subopenComparison, restrictIsoAlong,
    transportRestrictIso, restrictLocalIso, Category.assoc]

theorem chartComparisonIso_eq_along {X U V : Scheme} {E F : X.Modules}
    (i : U ⟶ X) (j : V ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j]
    (c : U ≅ V) (hc : c.hom ≫ j = i) (e : E.restrict j ≅ F.restrict j) :
    chartComparisonIso i j c hc e = restrictIsoAlong c.hom j i hc e := by
  apply Iso.ext
  simp [chartComparisonIso, restrictIsoAlong, transportRestrictIso,
    restrictLocalIso, Category.assoc]

/-- Restriction along a specified immersion is unchanged when its factor map is replaced
by an equal map. The result keeps the same target immersion, so no implicit transport is hidden. -/
theorem restrictIsoAlong_congr {X U V : Scheme} {E F : X.Modules}
    {f g : V ⟶ U} (hfg : f = g) (j : U ⟶ X) (i : V ⟶ X)
    [IsOpenImmersion f] [IsOpenImmersion g]
    [IsOpenImmersion j] [IsOpenImmersion i]
    (hf : f ≫ j = i) (hg : g ≫ j = i) (e : E.restrict j ≅ F.restrict j) :
    restrictIsoAlong f j i hf e = restrictIsoAlong g j i hg e := by
  subst g
  rfl

/-- A single overlap equation suffices to glue isomorphisms on two covering opens. -/
def glueOpenPairIso {X : Scheme} {E F : X.Modules} (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) (eU : E.restrict U.ι ≅ F.restrict U.ι)
    (eV : E.restrict V.ι ≅ F.restrict V.ι)
    (h : restrictOpenIso (homOfLE (inf_le_left : U ⊓ V ≤ U)) eU =
      restrictOpenIso (homOfLE (inf_le_right : U ⊓ V ≤ V)) eV) : E ≅ F := by
  let O : Fin 2 → X.Opens := Fin.cases U (fun _ => V)
  have hc : iSup O = ⊤ := by
    apply le_antisymm le_top
    rw [← hcover]
    exact sup_le (le_iSup O 0) (le_iSup O 1)
  let e : ∀ i, E.restrict (O i).ι ≅ F.restrict (O i).ι :=
    Fin.cases eU (fun _ => eV)
  apply glueOpenIso O hc e
  intro i j
  fin_cases i <;> fin_cases j
  · rfl
  · exact h
  · change restrictOpenIso (homOfLE (inf_le_left : V ⊓ U ≤ V)) eV =
      restrictOpenIso (homOfLE (inf_le_right : V ⊓ U ≤ U)) eU
    have hs : ∀ (Z : X.Opens) (hZV : Z ≤ V) (hZU : Z ≤ U), Z = U ⊓ V →
        restrictOpenIso (homOfLE hZV) eV = restrictOpenIso (homOfLE hZU) eU := by
      intro Z hZV hZU hZ
      subst Z
      exact h.symm
    exact hs (V ⊓ U) inf_le_left inf_le_right (inf_comm V U)
  · rfl

/-- Actual chart isomorphisms glue when their restrictions agree on a common presentation
of the full chart intersection. -/
def glueTwoChartIso {X A B W : Scheme} {E F : X.Modules}
    (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (j0 : A ⟶ X) (j1 : B ⟶ X) [IsOpenImmersion j0] [IsOpenImmersion j1]
    (c0 : U.toScheme ≅ A) (c1 : V.toScheme ≅ B)
    (hc0 : c0.hom ≫ j0 = U.ι) (hc1 : c1.hom ≫ j1 = V.ι)
    (k : W ≅ (U ⊓ V).toScheme)
    (f0 : W ⟶ A) (f1 : W ⟶ B) [IsOpenImmersion f0] [IsOpenImmersion f1]
    (hf0 : k.hom ≫ X.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫ c0.hom = f0)
    (hf1 : k.hom ≫ X.homOfLE (inf_le_right : U ⊓ V ≤ V) ≫ c1.hom = f1)
    (hcomp : f0 ≫ j0 = f1 ≫ j1)
    (e0 : E.restrict j0 ≅ F.restrict j0) (e1 : E.restrict j1 ≅ F.restrict j1)
    (h : restrictLocalIso f0 j0 e0 =
      transportRestrictIso hcomp.symm (restrictLocalIso f1 j1 e1)) : E ≅ F := by
  let eU := chartComparisonIso U.ι j0 c0 hc0 e0
  let eV := chartComparisonIso V.ι j1 c1 hc1 e1
  apply glueOpenPairIso U V hcover eU eV
  have hk : k.hom ≫ (U ⊓ V).ι = f0 ≫ j0 := by
    rw [← hf0]
    simp only [Category.assoc, hc0, X.homOfLE_ι]
  apply restrictIsoAlong_injective k (U ⊓ V).ι (f0 ≫ j0) hk
  have h0 : restrictIsoAlong k.hom (U ⊓ V).ι (f0 ≫ j0) hk
      (restrictOpenIso (homOfLE (inf_le_left : U ⊓ V ≤ U)) eU) =
        restrictLocalIso f0 j0 e0 := by
    rw [restrictOpenIso_eq_along]
    dsimp only [eU]
    rw [chartComparisonIso_eq_along, restrictIsoAlong_comp, restrictIsoAlong_comp]
    have hproj : (k.hom ≫ X.homOfLE (inf_le_left : U ⊓ V ≤ U)) ≫ c0.hom = f0 :=
      (Category.assoc _ _ _).trans hf0
    simpa only [restrictIsoAlong, transportRestrictIso_rfl] using
      restrictIsoAlong_congr hproj j0 (f0 ≫ j0)
        (congrArg (fun a => a ≫ j0) hproj) rfl e0
  have h1 : restrictIsoAlong k.hom (U ⊓ V).ι (f0 ≫ j0) hk
      (restrictOpenIso (homOfLE (inf_le_right : U ⊓ V ≤ V)) eV) =
        transportRestrictIso hcomp.symm (restrictLocalIso f1 j1 e1) := by
    rw [restrictOpenIso_eq_along]
    dsimp only [eV]
    rw [chartComparisonIso_eq_along, restrictIsoAlong_comp, restrictIsoAlong_comp]
    have hproj : (k.hom ≫ X.homOfLE (inf_le_right : U ⊓ V ≤ V)) ≫ c1.hom = f1 :=
      (Category.assoc _ _ _).trans hf1
    simpa only [restrictIsoAlong] using
      restrictIsoAlong_congr hproj j1 (f0 ≫ j0)
        ((congrArg (fun a => a ≫ j1) hproj).trans hcomp.symm) hcomp.symm e1
  exact h0.trans (h.trans h1.symm)


end LeBrunSalamon.ModuleGluing

end
/- END checked continuation glue_chart_iso.lean -/

/-! Integer powers of actual line bundles. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix

namespace LeBrunSalamon.LineBundleClasses

/-- Isomorphism of the underlying actual module sheaves. -/
def lineIsoSetoid (X : Scheme) : Setoid (LineBundle X) where
  r L M := Nonempty (L.sheaf ≅ M.sheaf)
  iseqv :=
    { refl := fun L => ⟨Iso.refl L.sheaf⟩
      symm := by
        intro L M h
        obtain ⟨e⟩ := h
        exact ⟨e.symm⟩
      trans := by
        intro L M N hLM hMN
        obtain ⟨e⟩ := hLM
        obtain ⟨f⟩ := hMN
        exact ⟨e ≪≫ f⟩ }

/-- Isomorphism classes of the existing line bundles on a scheme. -/
abbrev LineClass (X : Scheme) := Quotient (lineIsoSetoid X)

def classOf {X : Scheme} (L : LineBundle X) : LineClass X :=
  Quotient.mk (lineIsoSetoid X) L

theorem classOf_eq_iff {X : Scheme} (L M : LineBundle X) :
    classOf L = classOf M ↔ Nonempty (L.sheaf ≅ M.sheaf) := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound (s := lineIsoSetoid X) h

/-- Isomorphic line sheaves have isomorphic chosen dual sheaves. -/
def dualCongrIso {X : Scheme} {L M : LineBundle X} (e : L.sheaf ≅ M.sheaf) :
    (dualLine L).sheaf ≅ (dualLine M).sheaf :=
  (internalHomPresentation L.sheaf (structureModule X)).mapIso
    (internalHomPresentation M.sheaf (structureModule X)) e (Iso.refl _)

instance lineClassMul {X : Scheme} : Mul (LineClass X) :=
  ⟨Quotient.map₂ (fun L M : LineBundle X => tensorLine L M) (by
    intro L L' hL M M' hM
    obtain ⟨e⟩ := hL
    obtain ⟨f⟩ := hM
    exact ⟨PhaseTwentyFive.tensorIso e f⟩)⟩

instance lineClassOne {X : Scheme} : One (LineClass X) := ⟨classOf (trivialLine X)⟩

instance lineClassInv {X : Scheme} : Inv (LineClass X) :=
  ⟨Quotient.map (fun L : LineBundle X => dualLine L) (by
    intro L M h
    obtain ⟨e⟩ := h
    exact ⟨dualCongrIso (L := L) (M := M) e⟩)⟩

@[simp] theorem classOf_tensor {X : Scheme} (L M : LineBundle X) :
    classOf (tensorLine L M) = classOf L * classOf M := rfl

@[simp] theorem classOf_trivial (X : Scheme) :
    classOf (trivialLine X) = 1 := rfl

@[simp] theorem classOf_dual {X : Scheme} (L : LineBundle X) :
    classOf (dualLine L) = (classOf L)⁻¹ := rfl

/-- Tensor product and the actual chosen dual give the group of line-bundle classes. -/
instance lineClassCommGroup {X : Scheme} : CommGroup (LineClass X) where
  mul_assoc a b c := Quotient.inductionOn₃ a b c (fun L M N =>
    Quotient.sound (tensorSheaf_assoc L.sheaf M.sheaf N.sheaf))
  one_mul a := Quotient.inductionOn a (fun L =>
    Quotient.sound (tensorSheaf_leftUnit L.sheaf))
  mul_one a := Quotient.inductionOn a (fun L =>
    Quotient.sound (tensorSheaf_rightUnit L.sheaf))
  inv_mul_cancel a := Quotient.inductionOn a (fun L =>
    Quotient.sound (line_dual_evaluation L))
  mul_comm a b := Quotient.inductionOn₂ a b (fun L M =>
    Quotient.sound (tensorSheaf_comm L.sheaf M.sheaf))

/-- The original natural-power recursion computes powers in the class group. -/
@[simp] theorem classOf_linePower {X : Scheme} (L : LineBundle X) (n : ℕ) :
    classOf (linePower L n) = (classOf L) ^ n := by
  induction n with
  | zero => simp only [linePower, classOf_trivial, pow_zero]
  | succ n ih => simp only [linePower, classOf_tensor, ih, pow_succ]

/-- The original negative-power convention agrees with integer powers of the class. -/
@[simp] theorem classOf_linePowerInt {X : Scheme} (L : LineBundle X) (a : ℤ) :
    classOf (linePowerInt L a) = (classOf L) ^ a := by
  cases a with
  | ofNat n =>
      simpa only [linePowerInt, Int.ofNat_eq_natCast, zpow_natCast] using
        classOf_linePower L n
  | negSucc n =>
      simp only [linePowerInt, classOf_linePower, classOf_dual, zpow_negSucc, inv_pow]

/-- Tensoring with an actual line bundle reflects isomorphism classes. -/
theorem tensorLine_cancel_right {X : Scheme} (L M N : LineBundle X) :
    Nonempty ((tensorLine L N).sheaf ≅ (tensorLine M N).sheaf) ↔
      Nonempty (L.sheaf ≅ M.sheaf) := by
  rw [← classOf_eq_iff (tensorLine L N) (tensorLine M N), ← classOf_eq_iff L M]
  simp only [classOf_tensor, mul_right_cancel_iff]

theorem tensorLine_cancel_left {X : Scheme} (L M N : LineBundle X) :
    Nonempty ((tensorLine N L).sheaf ≅ (tensorLine N M).sheaf) ↔
      Nonempty (L.sheaf ≅ M.sheaf) := by
  rw [← classOf_eq_iff (tensorLine N L) (tensorLine N M), ← classOf_eq_iff L M]
  simp only [classOf_tensor, mul_left_cancel_iff]

theorem tensorLine_dual {X : Scheme} (L M : LineBundle X) :
    Nonempty ((dualLine (tensorLine L M)).sheaf ≅
      (tensorLine (dualLine L) (dualLine M)).sheaf) := by
  apply (classOf_eq_iff (dualLine (tensorLine L M))
    (tensorLine (dualLine L) (dualLine M))).mp
  simp only [classOf_dual, classOf_tensor, mul_inv]

theorem dualLine_trivial (X : Scheme) :
    Nonempty ((dualLine (trivialLine X)).sheaf ≅ (trivialLine X).sheaf) := by
  apply (classOf_eq_iff (dualLine (trivialLine X)) (trivialLine X)).mp
  simp only [classOf_dual, classOf_trivial, inv_one]

theorem linePower_dual {X : Scheme} (L : LineBundle X) (n : ℕ) :
    Nonempty ((dualLine (linePower L n)).sheaf ≅
      (linePower (dualLine L) n).sheaf) := by
  apply (classOf_eq_iff (dualLine (linePower L n)) (linePower (dualLine L) n)).mp
  simp only [classOf_dual, classOf_linePower, inv_pow]

theorem linePowerInt_congr {X : Scheme} {L M : LineBundle X}
    (e : L.sheaf ≅ M.sheaf) (a : ℤ) :
    Nonempty ((linePowerInt L a).sheaf ≅ (linePowerInt M a).sheaf) := by
  apply (classOf_eq_iff (linePowerInt L a) (linePowerInt M a)).mp
  rw [classOf_linePowerInt, classOf_linePowerInt,
    (classOf_eq_iff L M).mpr ⟨e⟩]

/-- Addition of arbitrary integer exponents for the existing actual line powers. -/
theorem linePowerInt_add {X : Scheme} (L : LineBundle X) (a b : ℤ) :
    Nonempty ((tensorLine (linePowerInt L a) (linePowerInt L b)).sheaf ≅
      (linePowerInt L (a + b)).sheaf) := by
  apply (classOf_eq_iff (tensorLine (linePowerInt L a) (linePowerInt L b))
    (linePowerInt L (a + b))).mp
  simp only [classOf_tensor, classOf_linePowerInt, zpow_add]

/-- Duality negates the integer exponent. -/
theorem linePowerInt_dual {X : Scheme} (L : LineBundle X) (a : ℤ) :
    Nonempty ((dualLine (linePowerInt L a)).sheaf ≅
      (linePowerInt L (-a)).sheaf) := by
  apply (classOf_eq_iff (dualLine (linePowerInt L a)) (linePowerInt L (-a))).mp
  simp only [classOf_dual, classOf_linePowerInt, zpow_neg]

/-- Iterated integer powers multiply their exponents. -/
theorem linePowerInt_mul {X : Scheme} (L : LineBundle X) (a b : ℤ) :
    Nonempty ((linePowerInt (linePowerInt L a) b).sheaf ≅
      (linePowerInt L (a * b)).sheaf) := by
  apply (classOf_eq_iff (linePowerInt (linePowerInt L a) b) (linePowerInt L (a * b))).mp
  simp only [classOf_linePowerInt, zpow_mul]

theorem linePowerInt_tensor {X : Scheme} (L M : LineBundle X) (a : ℤ) :
    Nonempty ((linePowerInt (tensorLine L M) a).sheaf ≅
      (tensorLine (linePowerInt L a) (linePowerInt M a)).sheaf) := by
  apply (classOf_eq_iff (linePowerInt (tensorLine L M) a)
    (tensorLine (linePowerInt L a) (linePowerInt M a))).mp
  simp only [classOf_linePowerInt, classOf_tensor, mul_zpow]

end LeBrunSalamon.LineBundleClasses

end


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.P1Charts
open LeBrunSalamon.ModuleGluing

namespace LeBrunSalamon.P1Ideal

/-- Glue the normalized actual chart comparisons using the entire Laurent overlap. -/
def normalizedPointIdealIso
    {p q : Spec (CommRingCat.of ℂ) ⟶ lineScheme}
    (d : NormalizedPointIdealFrames p) (e : NormalizedPointIdealFrames q) :
    kernel (structurePushforwardMap p) ≅ kernel (structurePushforwardMap q) :=
  glueTwoChartIso (chartOpen 0) (chartOpen 1) chartOpen_zero_sup_one
    (polynomialChartInclusion 0) (polynomialChartInclusion 1)
    (polynomialChartIso 0) (polynomialChartIso 1)
    (polynomialChartIso_hom_inclusion 0) (polynomialChartIso_hom_inclusion 1)
    polynomialOverlapIsoInf polynomialOverlapToZero polynomialOverlapToOne
    polynomialOverlapIsoInf_toZero polynomialOverlapIsoInf_toOne
    polynomialOverlap_condition
    (d.frameZero.symm ≪≫ e.frameZero) (d.frameOne.symm ≪≫ e.frameOne)
    (pointIdealChartComparison_compatible d e)

end LeBrunSalamon.P1Ideal

end

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix

namespace LeBrunSalamon.LineBundleClasses

/-- The actual chosen internal Hom between two line bundles is a line bundle. -/
def homLine {X : Scheme} (L M : LineBundle X) : LineBundle X where
  sheaf := internalHomSheaf L.sheaf M.sheaf
  locallyFree := by
    simpa only [Nat.mul_one] using internalHom_locallyFree L.locallyFree M.locallyFree

/-- The original chosen evaluation is invertible for a line-bundle source. -/
def homLineEvaluationIso {X : Scheme} (L M : LineBundle X) :
    (tensorLine (homLine L M) L).sheaf ≅ M.sheaf := by
  letI := SheafTensor.LocalEvaluation.chosen_evaluation_isIso_of_rank_one
    M.sheaf L.locallyFree
  exact asIso (internalHomPresentation L.sheaf M.sheaf).evaluate

@[simp] theorem classOf_homLine {X : Scheme} (L M : LineBundle X) :
    classOf (homLine L M) = classOf M * (classOf L)⁻¹ := by
  apply eq_mul_inv_iff_mul_eq.mpr
  change classOf (tensorLine (homLine L M) L) = classOf M
  exact (classOf_eq_iff (tensorLine (homLine L M) L) M).mpr
    ⟨homLineEvaluationIso L M⟩

/-- The actual internal Hom of lines is isomorphic to the dual source tensored with the target. -/
theorem internalHom_line_tensor {X : Scheme} (L M : LineBundle X) :
    Nonempty (internalHomSheaf L.sheaf M.sheaf ≅
      (tensorLine (dualLine L) M).sheaf) := by
  apply (classOf_eq_iff (homLine L M) (tensorLine (dualLine L) M)).mp
  simpa only [classOf_homLine, classOf_tensor, classOf_dual] using
    mul_comm (classOf M) ((classOf L)⁻¹)

/-- Internal Hom of integer powers subtracts the source exponent from the target exponent. -/
theorem internalHom_linePowerInt {X : Scheme} (L : LineBundle X) (a b : ℤ) :
    Nonempty (internalHomSheaf (linePowerInt L a).sheaf (linePowerInt L b).sheaf ≅
      (linePowerInt L (b - a)).sheaf) := by
  apply (classOf_eq_iff (homLine (linePowerInt L a) (linePowerInt L b))
    (linePowerInt L (b - a))).mp
  simp only [classOf_homLine, classOf_linePowerInt, zpow_sub]

end LeBrunSalamon.LineBundleClasses

end


end



/- Source-only generation proof using one separately approved published input.
   The exact original PhaseTen declaration is relocated after its actual dependencies. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix

namespace LeBrunSalamon.PhaseTwentyEight

/-- **Published input (exact).** Nonvanishing of an invertible-sheaf
section commutes with pullback along any morphism of locally ringed spaces.
This is Stacks Project, Remark 17.25.11 (Tag 0H78), using the nonvanishing
open of Lemma 17.25.10 (Tag 01CY). -/
theorem _root_.LeBrunSalamon.PublishedInputs.ExternalTensorDiagonal.nonvanishingOpen_pullback
    {X Y : Scheme} (f : X ⟶ Y)
    (L : LineBundle Y) (s : AlgebraicSection L.sheaf) :
    f ⁻¹ᵁ nonvanishingOpen L s =
      nonvanishingOpen (pullbackLine f L) (pullSection f s) := by
  sorry

/-- Project API wrapper for pullback of the nonvanishing locus. -/
theorem nonvanishingOpen_pullback {X Y : Scheme} (f : X ⟶ Y)
    (L : LineBundle Y) (s : AlgebraicSection L.sheaf) :
    f ⁻¹ᵁ nonvanishingOpen L s =
      nonvanishingOpen (pullbackLine f L) (pullSection f s) :=
  LeBrunSalamon.PublishedInputs.ExternalTensorDiagonal.nonvanishingOpen_pullback f L s

namespace FirstJetGenerationProof

/-- A local rank-one frame restricts to an actual isomorphism on the entire
first infinitesimal neighbourhood, using its genuine factorization through the frame open. -/
theorem line_fatPoint_trivialization {d : ℕ} (X : SmoothProperComplexVariety d)
    (L : LineBundle X.scheme) (x : ComplexPoint X) :
    Nonempty (pullbackModule (pointPowerInclusion x 2) (structureModule X.scheme) ≅
      pullbackModule (pointPowerInclusion x 2) L.sheaf) := by
  obtain ⟨q, hq, hr⟩ := L.locallyFree
  letI := hq
  have hcover := (_root_.Opens.coversTop_iff X.scheme q.X).mp q.coversTop
  obtain ⟨i, hi⟩ := hcover.exists_mem (x.map (IsLocalRing.closedPoint ℂ))
  let U : X.scheme.Opens := q.X i
  have hxU : Set.range x.map ⊆ (U : Set X.scheme) := by
    rintro _ ⟨z, rfl⟩
    change x.map z ∈ U
    rw [Subsingleton.elim z (IsLocalRing.closedPoint ℂ)]
    exact hi
  let g := FatPointOpenFactorizationProof.pointPowerLift x 2 (by decide) U hxU
  have hg : g ≫ U.ι = pointPowerInclusion x 2 :=
    FatPointOpenFactorizationProof.pointPowerLift_fac x 2 (by decide) U hxU
  let e : pullbackModule U.ι (structureModule X.scheme) ≅
      pullbackModule U.ι L.sheaf :=
    unitPullbackIso U.ι ≪≫
      (coproductUniqueIso (fun _ : Fin 1 => structureModule U.toScheme)).symm ≪≫
      DominantSectionInjectivityProof.localFreePullbackIso q hr i
  let c (E : OModule X.scheme) :
      pullbackModule g (pullbackModule U.ι E) ≅
        pullbackModule (pointPowerInclusion x 2) E :=
    (Scheme.Modules.pullbackComp g U.ι).app E ≪≫
      (Scheme.Modules.pullbackCongr hg).app E
  exact ⟨(c (structureModule X.scheme)).symm ≪≫
    (Scheme.Modules.pullback g).mapIso e ≪≫ c L.sheaf⟩

/-- First-jet surjectivity produces a global section that is invertible at
the specified complex point, without replacing the fat point by its reduction. -/
theorem firstJet_exists_nonvanishing {d : ℕ} (X : SmoothProperComplexVariety d)
    (L : LineBundle X.scheme) (h : SeparatesFirstJets X L) (x : ComplexPoint X) :
    ∃ s : AlgebraicSection L.sheaf,
      x.map (IsLocalRing.closedPoint ℂ) ∈ nonvanishingOpen L s := by
  obtain ⟨e⟩ := line_fatPoint_trivialization X L x
  obtain ⟨s, hs⟩ := h x e.hom
  have hraw : IsIso (restrictSection (pointPowerInclusion x 2) s) := by
    change IsIso (jetRestrictionAt x L.sheaf 1 s)
    rw [hs]
    infer_instance
  have hnormalized : IsIso (pullSection (pointPowerInclusion x 2) s) := by
    letI := hraw
    unfold pullSection
    infer_instance
  have htop := (nonvanishingOpen_eq_top_iff
    (pullbackLine (pointPowerInclusion x 2) L)
    (pullSection (pointPowerInclusion x 2) s)).mpr hnormalized
  rw [← nonvanishingOpen_pullback] at htop
  letI : IsClosedImmersion x.map :=
    FatPointOpenFactorizationProof.complexPoint_isClosedImmersion x
  have hrange : Set.range x.map ⊆ Set.range (pointPowerInclusion x 2) :=
    (FatPointOpenFactorizationProof.kernelPowerInclusion_range x.map 2 (by decide)).symm.le
  obtain ⟨z, hz⟩ := hrange ⟨IsLocalRing.closedPoint ℂ, rfl⟩
  refine ⟨s, ?_⟩
  rw [← hz]
  change z ∈ pointPowerInclusion x 2 ⁻¹ᵁ nonvanishingOpen L s
  rw [htop]
  trivial

/-- The actual global section morphisms yield an epimorphism from a free
sheaf when their genuine nonvanishing opens cover the scheme. -/
theorem globallyGenerated_of_nonvanishing_cover {X : Scheme} (L : LineBundle X)
    (h : ∀ x : X, ∃ s : AlgebraicSection L.sheaf, x ∈ nonvanishingOpen L s) :
    IsGloballyGenerated L.sheaf := by
  apply LeBrunSalamon.PhaseNine.ClosedPointGenerationProof.globallyGenerated_of_locally_isIso_section
  intro x
  obtain ⟨s, hs⟩ := h x
  let U := nonvanishingOpen L s
  refine ⟨U, s, hs, ?_⟩
  let A := (Scheme.Modules.overEquiv U).functor
  let e := Scheme.Modules.overFunctorEquiv U ≪≫
    Scheme.Modules.restrictFunctorIsoPullback U.ι
  letI : IsIso (A.map (s.over U)) :=
    (NatIso.isIso_map_iff e s).mpr (nonvanishingOpen_isIso L s)
  exact isIso_of_reflects_iso (s.over U) A

end FirstJetGenerationProof
end LeBrunSalamon.PhaseTwentyEight

namespace LeBrunSalamon.PhaseTen

open LeBrunSalamon.PhaseTwentyEight

/-- An elementary but important implication: if a line bundle separates first jets everywhere then it is
globally generated. The proof uses coherence, local freeness and the reduction to all closed points of a
finite-type complex scheme, not merely a definition unfolding. -/
theorem separatesFirstJets_implies_globallyGenerated
    {d : ℕ} (X : SmoothProperComplexVariety d)
    (L : LineBundle X.scheme)
    (h : SeparatesFirstJets X L) :
    IsGloballyGenerated L.sheaf := by
  let U : X.scheme.Opens := ⨆ s : AlgebraicSection L.sheaf, nonvanishingOpen L s
  have htop : U = ⊤ := by
    apply LeBrunSalamon.PhaseNine.ClosedPointGenerationProof.open_eq_top_of_complexPoints X
    intro x
    obtain ⟨s, hs⟩ := FirstJetGenerationProof.firstJet_exists_nonvanishing X L h x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨s, hs⟩
  apply FirstJetGenerationProof.globallyGenerated_of_nonvanishing_cover L
  intro x
  have hx : x ∈ U := by rw [htop]; trivial
  exact TopologicalSpace.Opens.mem_iSup.mp hx

end LeBrunSalamon.PhaseTen
end

