import LSP1BivectorCoordinates

/-!
# Comparing the two actual projective coordinate presentations

The polynomial charts of the original Proj construction and the ratio
charts of the chosen universal quotient are related by an actual
automorphism over C.  Both directions are glued from the same affine
line, and the overlap comparison is proved over arbitrary test schemes
using the actual Laurent coordinate.  This retains the chosen quotient
used in the standard conic equation.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.Core LeBrunSalamon.Skeleton LeBrunSalamon.P1Charts
open LeBrunSalamon.Construction.Smoothing.CoordinateCharts
open LeBrunSalamon.Construction.Smoothing.SourceAffineCharts
open scoped LaurentPolynomial

namespace LeBrunSalamon.Construction.P1CoordinateGauge

abbrev P := Lines.P
abbrev LaurentLine := Spec (CommRingCat.of ℂ[T;T⁻¹])

def laurentFunction (p : ℂ[T;T⁻¹]) : RingSections LaurentLine ⊤ :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ[T;T⁻¹])).inv p

theorem overlapZero_apply (p : Polynomial ℂ) :
    polynomialOverlapToZero.appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))).inv p) =
        laurentFunction (Polynomial.toLaurent p) := by
  exact (congrArg (fun k : CommRingCat.of (Polynomial ℂ) ⟶
      LaurentLine.presheaf.obj (op ⊤) => k p)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
      (Polynomial.toLaurent : Polynomial ℂ →+* ℂ[T;T⁻¹])))).symm

theorem overlapOne_apply (p : Polynomial ℂ) :
    polynomialOverlapToOne.appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))).inv p) =
        laurentFunction (LaurentPolynomial.invert (Polynomial.toLaurent p)) := by
  exact (congrArg (fun k : CommRingCat.of (Polynomial ℂ) ⟶
      LaurentLine.presheaf.obj (op ⊤) => k p)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
      (LaurentPolynomial.invert.toRingHom.comp
        (Polynomial.toLaurent : Polynomial ℂ →+* ℂ[T;T⁻¹]))))).symm

theorem overlap_parameter_product :
    polynomialOverlapToZero.appTop parameterFunction *
        polynomialOverlapToOne.appTop parameterFunction = 1 := by
  rw [parameterFunction, overlapZero_apply, overlapOne_apply]
  simp only [Polynomial.toLaurent_X, LaurentPolynomial.invert_T]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ[T;T⁻¹])).inv
      (LaurentPolynomial.T 1) *
    (Scheme.ΓSpecIso (CommRingCat.of ℂ[T;T⁻¹])).inv
      (LaurentPolynomial.T (-1)) = 1
  rw [← map_mul, ← LaurentPolynomial.T_add]
  norm_num

/-- The actual map into the Laurent overlap from a unit on any scheme. -/
def fromUnit {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (u : (RingSections Y ⊤)ˣ) : Y ⟶ LaurentLine :=
  (ΓSpec.adjunction.homEquiv Y (op (CommRingCat.of ℂ[T;T⁻¹])))
    (CommRingCat.ofHom (LaurentPolynomial.eval₂ (complexConstants sY) u)).op

theorem fromUnit_apply {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (u : (RingSections Y ⊤)ˣ) (p : ℂ[T;T⁻¹]) :
    (fromUnit sY u).appTop (laurentFunction p) =
      LaurentPolynomial.eval₂ (complexConstants sY) u p := by
  exact congrArg (fun k : CommRingCat.of ℂ[T;T⁻¹] ⟶
      Y.presheaf.obj (op ⊤) => k p)
    (ΓSpecIso_inv_ΓSpec_adjunction_homEquiv (CommRingCat.ofHom
      (LaurentPolynomial.eval₂ (complexConstants sY) u)))

theorem fromUnit_zero {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (u : (RingSections Y ⊤)ˣ) :
    fromUnit sY u ≫ polynomialOverlapToZero = fromFunction sY u := by
  apply ext_to_Spec
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro c
    change (fromUnit sY u).appTop
      (polynomialOverlapToZero.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))).inv (Polynomial.C c))) = _
    rw [overlapZero_apply, fromUnit_apply, fromFunction_apply,
      LaurentPolynomial.eval₂_toLaurent]
  · change (fromUnit sY u).appTop
        (polynomialOverlapToZero.appTop parameterFunction) = _
    rw [parameterFunction, overlapZero_apply, fromUnit_apply, fromFunction_apply,
      LaurentPolynomial.eval₂_toLaurent]

theorem fromUnit_one {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (u : (RingSections Y ⊤)ˣ) :
    fromUnit sY u ≫ polynomialOverlapToOne = fromFunction sY (↑u⁻¹) := by
  apply ext_to_Spec
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro c
    change (fromUnit sY u).appTop
      (polynomialOverlapToOne.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))).inv (Polynomial.C c))) = _
    rw [overlapOne_apply, fromUnit_apply, fromFunction_apply]
    simp
  · change (fromUnit sY u).appTop
        (polynomialOverlapToOne.appTop parameterFunction) = _
    rw [parameterFunction, overlapOne_apply, fromUnit_apply, fromFunction_apply]
    simp

/-- The reciprocal identity in the canonical Proj charts, including
nilpotent test schemes. -/
theorem canonical_reciprocal {Y : Scheme} (sY : Y ⟶ ComplexBase)
    (a b : Y ⟶ AffineLine) (ha : a ≫ affineLineToC = sY)
    (hb : b ≫ affineLineToC = sY)
    (hab : a.appTop parameterFunction * b.appTop parameterFunction = 1) :
    a ≫ polynomialChartInclusion 0 = b ≫ polynomialChartInclusion 1 := by
  let u : (RingSections Y ⊤)ˣ :=
    ⟨a.appTop parameterFunction, b.appTop parameterFunction, hab,
      by simpa only [mul_comm] using hab⟩
  have h0 : fromUnit sY u ≫ polynomialOverlapToZero = a := by
    rw [fromUnit_zero]
    exact (fromFunction_unique sY _ a ha rfl).symm
  have h1 : fromUnit sY u ≫ polynomialOverlapToOne = b := by
    rw [fromUnit_one]
    exact (fromFunction_unique sY _ b hb rfl).symm
  rw [← h0, ← h1]
  simpa only [Category.assoc] using
    congrArg (fun f => fromUnit sY u ≫ f) polynomialOverlap_condition

/-- Equality in two canonical charts factors through their complete
scheme-theoretic Laurent overlap, not just their complex points. -/
theorem canonical_overlap_factors {Y : Scheme} (a b : Y ⟶ AffineLine)
    (h : a ≫ polynomialChartInclusion 0 = b ≫ polynomialChartInclusion 1) :
    ∃ q : Y ⟶ LaurentLine,
      q ≫ polynomialOverlapToZero = a ∧ q ≫ polynomialOverlapToOne = b := by
  have hr : Set.range (a ≫ polynomialChartInclusion 0) ⊆
      Set.range (polynomialOverlapToZero ≫ polynomialChartInclusion 0) := by
    change Set.range (a ≫ polynomialChartInclusion 0) ⊆
      ((polynomialOverlapToZero ≫ polynomialChartInclusion 0).opensRange :
        Set ProjectiveLine)
    rw [polynomialOverlap_range]
    rintro _ ⟨y, rfl⟩
    constructor
    · change polynomialChartInclusion 0 (a y) ∈ chartOpen 0
      rw [← polynomialChartInclusion_range]
      exact ⟨a y, rfl⟩
    · rw [h]
      change polynomialChartInclusion 1 (b y) ∈ chartOpen 1
      rw [← polynomialChartInclusion_range]
      exact ⟨b y, rfl⟩
  let q := IsOpenImmersion.lift
    (polynomialOverlapToZero ≫ polynomialChartInclusion 0)
    (a ≫ polynomialChartInclusion 0) hr
  have hq : q ≫ polynomialOverlapToZero ≫ polynomialChartInclusion 0 =
      a ≫ polynomialChartInclusion 0 := IsOpenImmersion.lift_fac _ _ _
  refine ⟨q, ?_, ?_⟩
  · apply (cancel_mono (polynomialChartInclusion 0)).mp
    simpa only [Category.assoc] using hq
  · apply (cancel_mono (polynomialChartInclusion 1)).mp
    rw [Category.assoc, ← polynomialOverlap_condition, hq, h]

theorem canonical_overlap_product {Y : Scheme} (a b : Y ⟶ AffineLine)
    (h : a ≫ polynomialChartInclusion 0 = b ≫ polynomialChartInclusion 1) :
    a.appTop parameterFunction * b.appTop parameterFunction = 1 := by
  obtain ⟨q, h0, h1⟩ := canonical_overlap_factors a b h
  rw [← h0, ← h1]
  change q.appTop (polynomialOverlapToZero.appTop parameterFunction) *
    q.appTop (polynomialOverlapToOne.appTop parameterFunction) = 1
  rw [← map_mul, overlap_parameter_product, map_one]

/-- Invertible quotient sections give reciprocal actual regular ratios. -/
theorem ratioFunction_product {Y : Scheme} (f : Y ⟶ ProjectiveLine)
    [IsIso (pullSection f ((projectiveCoordinates 1).coordinate 0))]
    [IsIso (pullSection f ((projectiveCoordinates 1).coordinate 1))] :
    ratioFunction f 0 * ratioFunction f 1 = 1 := by
  have hs : scalarSection (ratioFunction f 0 * ratioFunction f 1) =
      scalarSection (1 : RingSections Y ⊤) := by
    rw [scalarSection_mul]
    simp only [ratioFunction, other, if_pos rfl, show (1 : Fin 2) ≠ 0 by decide,
      if_neg, scalarSection, sectionFromValue_sectionValue,
      Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]
    exact (scalarSection_one Y).symm
  simpa only [scalarSection, sectionFromValue_spec] using congrArg sectionValue hs

theorem ratio_overlap_product {Y : Scheme} (a b : Y ⟶ AffineLine)
    (h : a ≫ (ratioPoint 0).val = b ≫ (ratioPoint 1).val) :
    a.appTop parameterFunction * b.appTop parameterFunction = 1 := by
  letI := ratioPull_self_isIso a 0
  letI := ratioPull_self_isIso b 1
  have hi : IsIso (pullSection (a ≫ (ratioPoint 0).val)
      ((projectiveCoordinates 1).coordinate 1)) := by rw [h]; infer_instance
  letI := hi
  have hp := ratioFunction_product (a ≫ (ratioPoint 0).val)
  rw [ratioFunction_comp] at hp
  have hb : ratioFunction (a ≫ (ratioPoint 0).val) 1 =
      b.appTop parameterFunction := by rw [h, ratioFunction_comp]
  simpa only [hb] using hp

def canonicalCover : ProjectiveLine.OpenCover where
  I₀ := Fin 2
  X i := (chartOpen i).toScheme
  f i := (chartOpen i).ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro x
    have hx : x ∈ (⨆ i : Fin 2, chartOpen i) := by rw [chartOpen_cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨i, ⟨⟨x, hi⟩, rfl⟩⟩

def quotientCover : ProjectiveLine.OpenCover where
  I₀ := Fin 2
  X i := (ratioOpen i).toScheme
  f i := (ratioOpen i).ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro x
    have hx : x ∈ (⨆ i : Fin 2, ratioOpen i) := by rw [ratioOpen_cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨i, ⟨⟨x, hi⟩, rfl⟩⟩

def forwardChart (i : Fin 2) : (chartOpen i).toScheme ⟶ ProjectiveLine :=
  (polynomialChartIso i).hom ≫ (ratioPoint i).val

def inverseChart (i : Fin 2) : (ratioOpen i).toScheme ⟶ ProjectiveLine :=
  (ratioOpenIso i).hom ≫ polynomialChartInclusion i

theorem forwardChart_compatible {Y : Scheme} (i j : Fin 2)
    (a : Y ⟶ (chartOpen i).toScheme) (b : Y ⟶ (chartOpen j).toScheme)
    (h : a ≫ (chartOpen i).ι = b ≫ (chartOpen j).ι) :
    a ≫ forwardChart i = b ≫ forwardChart j := by
  have mixed {T : Scheme} (a : T ⟶ (chartOpen 0).toScheme)
      (b : T ⟶ (chartOpen 1).toScheme)
      (h : a ≫ (chartOpen 0).ι = b ≫ (chartOpen 1).ι) :
      a ≫ forwardChart 0 = b ≫ forwardChart 1 := by
    let u := a ≫ (polynomialChartIso 0).hom
    let v := b ≫ (polynomialChartIso 1).hom
    have huv : u ≫ polynomialChartInclusion 0 = v ≫ polynomialChartInclusion 1 := by
      simpa only [u, v, polynomialChartInclusion, Category.assoc,
        Iso.hom_inv_id_assoc] using h
    have hu : u ≫ affineLineToC = (u ≫ polynomialChartInclusion 0) ≫ P.structureMap := by
      rw [Category.assoc, polynomialChartInclusion_baseMap]
      rfl
    have hv : v ≫ affineLineToC = (u ≫ polynomialChartInclusion 0) ≫ P.structureMap := by
      rw [huv, Category.assoc, polynomialChartInclusion_baseMap]
      rfl
    have hp := canonical_overlap_product u v huv
    have hc := Smoothing.PuncturedSourceProof.reciprocal_ratios
      ((u ≫ polynomialChartInclusion 0) ≫ P.structureMap) v u hv hu
      (by simpa only [mul_comm] using hp)
    simpa only [forwardChart, u, v, Category.assoc] using hc.symm
  fin_cases i <;> fin_cases j
  · rw [(cancel_mono (chartOpen 0).ι).mp h]
  · exact mixed a b h
  · exact (mixed b a h.symm).symm
  · rw [(cancel_mono (chartOpen 1).ι).mp h]

theorem inverseChart_compatible {Y : Scheme} (i j : Fin 2)
    (a : Y ⟶ (ratioOpen i).toScheme) (b : Y ⟶ (ratioOpen j).toScheme)
    (h : a ≫ (ratioOpen i).ι = b ≫ (ratioOpen j).ι) :
    a ≫ inverseChart i = b ≫ inverseChart j := by
  have mixed {T : Scheme} (a : T ⟶ (ratioOpen 0).toScheme)
      (b : T ⟶ (ratioOpen 1).toScheme)
      (h : a ≫ (ratioOpen 0).ι = b ≫ (ratioOpen 1).ι) :
      a ≫ inverseChart 0 = b ≫ inverseChart 1 := by
    let u := a ≫ (ratioOpenIso 0).hom
    let v := b ≫ (ratioOpenIso 1).hom
    have huv : u ≫ (ratioPoint 0).val = v ≫ (ratioPoint 1).val := by
      simpa only [u, v, ratioOpenIso, Category.assoc, openToRatio_point] using h
    have hu : u ≫ affineLineToC = (u ≫ (ratioPoint 0).val) ≫ P.structureMap := by
      rw [Category.assoc, (ratioPoint 0).property]
    have hv : v ≫ affineLineToC = (u ≫ (ratioPoint 0).val) ≫ P.structureMap := by
      rw [huv, Category.assoc, (ratioPoint 1).property]
    have hc := canonical_reciprocal ((u ≫ (ratioPoint 0).val) ≫ P.structureMap)
      u v hu hv (ratio_overlap_product u v huv)
    simpa only [inverseChart, u, v, Category.assoc] using hc
  fin_cases i <;> fin_cases j
  · rw [(cancel_mono (ratioOpen 0).ι).mp h]
  · exact mixed a b h
  · exact (mixed b a h.symm).symm
  · rw [(cancel_mono (ratioOpen 1).ι).mp h]

def forward : ProjectiveLine ⟶ ProjectiveLine :=
  canonicalCover.glueMorphisms forwardChart (fun i j =>
    forwardChart_compatible i j _ _ pullback.condition)

def backward : ProjectiveLine ⟶ ProjectiveLine :=
  quotientCover.glueMorphisms inverseChart (fun i j =>
    inverseChart_compatible i j _ _ pullback.condition)

@[reassoc]
theorem canonical_chart_forward (i : Fin 2) :
    (chartOpen i).ι ≫ forward = forwardChart i :=
  canonicalCover.ι_glueMorphisms _ _ i

@[reassoc]
theorem quotient_chart_backward (i : Fin 2) :
    (ratioOpen i).ι ≫ backward = inverseChart i :=
  quotientCover.ι_glueMorphisms _ _ i

@[reassoc]
theorem polynomial_forward (i : Fin 2) :
    polynomialChartInclusion i ≫ forward = (ratioPoint i).val := by
  rw [polynomialChartInclusion, Category.assoc, canonical_chart_forward, forwardChart,
    Iso.inv_hom_id_assoc]

@[reassoc]
theorem quotient_backward (i : Fin 2) :
    (ratioPoint i).val ≫ backward = polynomialChartInclusion i := by
  rw [← ratioToOpen_inclusion i, Category.assoc, quotient_chart_backward, inverseChart]
  change (ratioOpenIso i).inv ≫ (ratioOpenIso i).hom ≫ polynomialChartInclusion i = _
  rw [Iso.inv_hom_id_assoc]

theorem forward_backward : forward ≫ backward = 𝟙 ProjectiveLine := by
  apply canonicalCover.hom_ext
  intro i
  change (chartOpen i).ι ≫ (forward ≫ backward) = (chartOpen i).ι ≫ 𝟙 _
  rw [← Category.assoc, canonical_chart_forward, forwardChart, Category.assoc,
    quotient_backward, polynomialChartInclusion, Iso.hom_inv_id_assoc, Category.comp_id]

theorem backward_forward : backward ≫ forward = 𝟙 ProjectiveLine := by
  apply quotientCover.hom_ext
  intro i
  change (ratioOpen i).ι ≫ (backward ≫ forward) = (ratioOpen i).ι ≫ 𝟙 _
  rw [← Category.assoc, quotient_chart_backward, inverseChart, Category.assoc,
    polynomial_forward, Category.comp_id]
  exact openToRatio_point i

/-- The actual over-C coordinate gauge, proved from the two affine
charts and their complete Laurent overlap. -/
def iso : ProjectiveLine ≅ ProjectiveLine where
  hom := forward
  inv := backward
  hom_inv_id := forward_backward
  inv_hom_id := backward_forward

theorem iso_over : iso.hom ≫ P.structureMap = P.structureMap := by
  apply canonicalCover.hom_ext
  intro i
  change (chartOpen i).ι ≫ (forward ≫ P.structureMap) = (chartOpen i).ι ≫ P.structureMap
  rw [← Category.assoc, canonical_chart_forward, forwardChart, Category.assoc,
    (ratioPoint i).property]
  have h := congrArg (fun f => (polynomialChartIso i).hom ≫ f)
    (polynomialChartInclusion_baseMap i)
  simpa only [polynomialChartInclusion, Category.assoc, Iso.hom_inv_id_assoc] using h.symm

theorem iso_inverse_over : iso.inv ≫ P.structureMap = P.structureMap := by
  rw [← iso_over]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end LeBrunSalamon.Construction.P1CoordinateGauge

end
