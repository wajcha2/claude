import LSNodalFixedEnds

/-!
# The actual cotangent and logarithmic frames of the standard conic

The three source charts and the O(1,1) frames are fixed by the original
homogeneous quotient coordinates. The local coefficient below evaluates an
actual morphism out of the relative cotangent sheaf in precisely those
frames; it does not choose a coordinate derivation in place of that map.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseTwentyNine
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.PhaseThirtyFour LeBrunSalamon.Skeleton

namespace LeBrunSalamon.Construction.TraitContact

namespace RelativeBox

variable {S B : Scheme} (pi : S ⟶ B)

abbrev Square := pullback pi pi

abbrev first : Square pi ⟶ S := pullback.fst pi pi
abbrev second : Square pi ⟶ S := pullback.snd pi pi

def line (L : LineBundle S) : LineBundle (Square pi) :=
  tensorLine (pullbackLine (first pi) L) (pullbackLine (second pi) L)

def section {L : LineBundle S} (a b : AlgebraicSection L.sheaf) :
    AlgebraicSection (line pi L).sheaf :=
  tensorSection (pullSection (first pi) a) (pullSection (second pi) b)

/-- Canonical tensor/composition transport along an arbitrary test map
into the actual relative square. -/
def pullIso {T : Scheme} (f : T ⟶ Square pi) (L : LineBundle S) :
    pullbackModule f (line pi L).sheaf ≅
      tensorSheaf (pullbackModule (f ≫ first pi) L.sheaf)
        (pullbackModule (f ≫ second pi) L.sheaf) := by
  letI := tensorPullbackComparison_isIso f
    (pullbackModule (first pi) L.sheaf) (pullbackModule (second pi) L.sheaf)
  exact (asIso (tensorPullbackComparison f
    (pullbackModule (first pi) L.sheaf) (pullbackModule (second pi) L.sheaf))).symm ≪≫
      tensorIso
        (compositionPullback f (first pi) (f ≫ first pi) rfl L.sheaf)
        (compositionPullback f (second pi) (f ≫ second pi) rfl L.sheaf)

theorem pullIso_section {T : Scheme} (f : T ⟶ Square pi) {L : LineBundle S}
    (a b : AlgebraicSection L.sheaf) :
    pullSection f (section pi a b) ≫ (pullIso pi f L).hom =
      tensorSection (pullSection (f ≫ first pi) a)
        (pullSection (f ≫ second pi) b) := by
  letI := tensorPullbackComparison_isIso f
    (pullbackModule (first pi) L.sheaf) (pullbackModule (second pi) L.sheaf)
  rw [section, ← tensorPullbackComparison_onSections]
  simp only [pullIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
    Category.assoc, IsIso.hom_inv_id_assoc]
  rw [tensorSection_map, compositionPullback_sections, compositionPullback_sections]

end RelativeBox

end LeBrunSalamon.Construction.TraitContact

namespace LeBrunSalamon.Construction.StandardConicDifferential

open Smoothing Smoothing.CoordinateCharts Smoothing.SourceAffineCharts

variable (F : StandardSource)

/-- The actual homogeneous O(1,1) line on the represented conic. -/
def line : LineBundle F.source :=
  tensorLine (pullbackLine F.left (projectiveCoordinates 1).hyperplane)
    (pullbackLine F.right (projectiveCoordinates 1).hyperplane)

/-- The four actual homogeneous tensor-coordinate sections. -/
def coordinate (i j : Fin 2) : AlgebraicSection (line F).sheaf :=
  tensorSection (pullSection F.left ((projectiveCoordinates 1).coordinate i))
    (pullSection F.right ((projectiveCoordinates 1).coordinate j))

/-- Each displayed affine-plane chart is the actual open inclusion
after its already constructed isomorphism onto that open. -/
theorem modelMap_isOpenImmersion (k : Fin 3) :
    IsOpenImmersion (modelMap F k) := by
  have h : modelMap F k =
      (chartIso F k).inv ≫ (chartOpen F (leftIndex k) (rightIndex k)).ι :=
    (modelToChart_inclusion F k).symm
  rw [h]
  infer_instance

/-- The selected coordinate m_(leftIndex,rightIndex) is the unit
generator of the pulled line. Every composition and tensor comparison is
the canonical one used by the source's projective quotient coordinates. -/
def chartLineFrame (k : Fin 3) :
    pullbackModule (modelMap F k) (line F).sheaf ≅ structureModule Plane := by
  let c := modelMap F k
  let H := (projectiveCoordinates 1).hyperplane.sheaf
  letI := tensorPullbackComparison_isIso c
    (pullbackModule F.left H) (pullbackModule F.right H)
  exact (asIso (tensorPullbackComparison c
      (pullbackModule F.left H) (pullbackModule F.right H))).symm ≪≫
    tensorIso
      (compositionPullback c F.left
        (polynomialLine (leftPolynomial k) ≫ (ratioPoint (leftIndex k)).val)
        (modelMap_spec F k).2.1 H)
      (compositionPullback c F.right
        (polynomialLine (rightPolynomial k) ≫ (ratioPoint (rightIndex k)).val)
        (modelMap_spec F k).2.2 H) ≪≫
    productFrame (polynomialLine (leftPolynomial k))
      (polynomialLine (rightPolynomial k)) (leftIndex k) (rightIndex k)

theorem chartLineFrame_coordinate (k : Fin 3) (i j : Fin 2) :
    pullSection (modelMap F k) (coordinate F i j) ≫
        (chartLineFrame F k).hom =
      scalarSection
        (coefficient (leftIndex k) i (planeFunction (leftPolynomial k)) *
          coefficient (rightIndex k) j (planeFunction (rightPolynomial k))) := by
  letI := tensorPullbackComparison_isIso (modelMap F k)
    (pullbackModule F.left (projectiveCoordinates 1).hyperplane.sheaf)
    (pullbackModule F.right (projectiveCoordinates 1).hyperplane.sheaf)
  rw [coordinate, ← tensorPullbackComparison_onSections]
  simp only [chartLineFrame, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, tensorSection_map,
    compositionPullback_sections, compositionPullback_sections]
  change tensorSection _ _ ≫
    (tensorMap (ratioPullFrame _ _).hom (ratioPullFrame _ _).hom ≫
      (TensorConstruction.leftUnitIso (structureModule Plane)).hom) = _
  rw [← Category.assoc, tensorSection_map, ratioPullFrame_coefficient,
    ratioPullFrame_coefficient, tensorScalarSection,
    polynomialLine_parameter, polynomialLine_parameter]

theorem chartLineFrame_generator (k : Fin 3) :
    pullSection (modelMap F k)
        (coordinate F (leftIndex k) (rightIndex k)) =
      (chartLineFrame F k).inv := by
  apply (cancel_mono (chartLineFrame F k).hom).mp
  rw [chartLineFrame_coordinate, Iso.inv_hom_id]
  simp only [coefficient, if_pos rfl, one_mul, scalarSection_one]

/-- The source cotangent comparison is the actual differential of the
open immersion, not a separately supplied identification. -/
def chartCotangentIso (k : Fin 3) :
    pullbackModule (modelMap F k) (cotangentSheaf F.parameter) ≅
      cotangentSheaf (modelMap F k ≫ F.parameter) := by
  letI := modelMap_isOpenImmersion F k
  letI := openImmersion_cotangentMap_isIso (modelMap F k) F.parameter
  exact asIso (cotangentMap (modelMap F k) F.parameter)

/-- A cotangent-to-dual-line map transported to the actual affine chart. -/
def chartForm
    (q : cotangentSheaf F.parameter ⟶ dualSheaf (line F).sheaf) (k : Fin 3) :
    cotangentSheaf (modelMap F k ≫ F.parameter) ⟶
      dualSheaf (pullbackModule (modelMap F k) (line F).sheaf) :=
  (chartCotangentIso F k).inv ≫
    (Scheme.Modules.pullback (modelMap F k)).map q ≫
      dualBaseChange (modelMap F k) (line F).sheaf

/-- Coefficient of the actual differential dX_i against the selected
O(1,1) generator on the k-th actual affine-plane chart. -/
def chartCoefficient
    (q : cotangentSheaf F.parameter ⟶ dualSheaf (line F).sheaf)
    (k : Fin 3) (i : Fin 2) : RingSections Plane ⊤ :=
  (dualEvaluation (pullbackModule (modelMap F k) (line F).sheaf)).apply ⊤
    ((chartForm F q k).app ⊤
      ((cotangentPresentation (modelMap F k ≫ F.parameter)).differential.apply ⊤
        (planeFunction (MvPolynomial.X i))))
    (sectionValue (chartLineFrame F k).inv)

/-- At the node: (u,-v). At the left outer chart: (0,-1).
At the right outer chart: (0,1). The first outer coordinate is the
base parameter, so its relative differential has zero coefficient. -/
def chartLogValue (k : Fin 3) (i : Fin 2) : RingSections Plane ⊤ :=
  if k = 0 then
    (if i = 0 then planeFunction (MvPolynomial.X 0)
      else -planeFunction (MvPolynomial.X 1))
  else if i = 0 then 0 else if k = 1 then -1 else 1

/-- Transpose the actual dual evaluation pairing. Its normalization is
proved directly from the internal-Hom universal property. -/
def transpose {Y : Scheme} {E M : OModule Y} (q : E ⟶ dualSheaf M) :
    M ⟶ dualSheaf E :=
  currySheaf (tensorLift
    (TensorConstruction.flip ((dualEvaluation M).precompose q (𝟙 M))))

theorem transpose_evaluate {Y : Scheme} {E M : OModule Y}
    (q : E ⟶ dualSheaf M) (U : Y.Opens)
    (m : SectionsOn M U) (w : SectionsOn E U) :
    (dualEvaluation E).apply U ((transpose q).app U m) w =
      (dualEvaluation M).apply U (q.app U w) m := by
  let b := TensorConstruction.flip ((dualEvaluation M).precompose q (𝟙 M))
  have h := congrArg (fun f : tensorSheaf M E ⟶ structureModule Y =>
    f.app U ((tensorPresentation M E).pair.apply U m w))
      (currySheaf_evaluate (tensorLift b))
  rw [ContactDerivativeIsoProof.dual_uncurry_apply] at h
  exact h.trans (congrArg (fun p : SheafBilinearMap M E (structureModule Y) =>
    p.apply U m w) (tensorLift_pair b))

theorem transpose_zero {Y : Scheme} (E M : OModule Y) :
    transpose (0 : E ⟶ dualSheaf M) = 0 := by
  apply ContactDerivativeIsoProof.dual_hom_ext
  intro U m w
  rw [transpose_evaluate]
  simp

theorem transpose_comp {Y : Scheme} {E E' M : OModule Y}
    (a : E' ⟶ E) (q : E ⟶ dualSheaf M) :
    transpose (a ≫ q) = transpose q ≫ ContactDerivativeIsoProof.dualMap a := by
  apply ContactDerivativeIsoProof.dual_hom_ext
  intro U m w
  rw [transpose_evaluate]
  change (dualEvaluation M).apply U (q.app U (a.app U w)) m =
    (dualEvaluation E').apply U
      ((ContactDerivativeIsoProof.dualMap a).app U ((transpose q).app U m)) w
  rw [ContactDerivativeIsoProof.dualMap_evaluate, transpose_evaluate]

theorem transpose_dualMap {Y : Scheme} {E M M' : OModule Y}
    (q : E ⟶ dualSheaf M) (b : M' ⟶ M) :
    transpose (q ≫ ContactDerivativeIsoProof.dualMap b) = b ≫ transpose q := by
  apply ContactDerivativeIsoProof.dual_hom_ext
  intro U m w
  rw [transpose_evaluate]
  change (dualEvaluation M').apply U
    ((ContactDerivativeIsoProof.dualMap b).app U (q.app U w)) m =
      (dualEvaluation E).apply U ((transpose q).app U (b.app U m)) w
  rw [ContactDerivativeIsoProof.dualMap_evaluate, transpose_evaluate]

/-- Transposition commutes with actual pullback after the canonical dual
comparison. This statement does not assume that E is locally free. -/
theorem transpose_pullback {Y Z : Scheme} (f : Y ⟶ Z)
    {E M : OModule Z} (q : E ⟶ dualSheaf M) :
    (Scheme.Modules.pullback f).map (transpose q) ≫ dualBaseChange f E =
      transpose ((Scheme.Modules.pullback f).map q ≫ dualBaseChange f M) := by
  apply ContactDerivativeIsoProof.dual_pullback_hom_ext f M E
  intro U m w
  change (dualEvaluation (pullbackModule f E)).apply (f ⁻¹ᵁ U)
    ((dualBaseChange f E).app (f ⁻¹ᵁ U)
      (((Scheme.Modules.pullback f).map (transpose q)).app (f ⁻¹ᵁ U)
        (pullLocalSection f M U m))) (pullLocalSection f E U w) = _
  rw [ExternalExchangeCoherenceProof.pullLocalSection_map,
    ContactDerivativeIsoProof.dualBaseChange_evaluate, pullbackPair_normalized,
    ContactDerivativeIsoProof.unitPullbackMap_pullLocalSection,
    transpose_evaluate, transpose_evaluate]
  change f.app U ((dualEvaluation M).apply U (q.app U w) m) =
    (dualEvaluation (pullbackModule f M)).apply (f ⁻¹ᵁ U)
      ((dualBaseChange f M).app (f ⁻¹ᵁ U)
        (((Scheme.Modules.pullback f).map q).app (f ⁻¹ᵁ U)
          (pullLocalSection f E U w))) (pullLocalSection f M U m)
  rw [ExternalExchangeCoherenceProof.pullLocalSection_map,
    ContactDerivativeIsoProof.dualBaseChange_evaluate, pullbackPair_normalized,
    ContactDerivativeIsoProof.unitPullbackMap_pullLocalSection]

/-- The logarithmic tangent morphism determined by an actual source
fundamental-class map. It is defined on the whole conic. -/
def logMapFrom
    (q : cotangentSheaf F.parameter ⟶ dualSheaf (line F).sheaf) :
    (line F).sheaf ⟶ tangentSheaf F.parameter := transpose q

theorem logMapFrom_evaluate
    (q : cotangentSheaf F.parameter ⟶ dualSheaf (line F).sheaf)
    (U : F.source.Opens) (m : SectionsOn (line F).sheaf U)
    (w : SectionsOn (cotangentSheaf F.parameter) U) :
    (dualEvaluation (cotangentSheaf F.parameter)).apply U
        ((logMapFrom F q).app U m) w =
      (dualEvaluation (line F).sheaf).apply U (q.app U w) m :=
  transpose_evaluate q U m w

namespace Numerator

open TraitContact

abbrev Square := RelativeBox.Square F.parameter

abbrev squareProjection : Square F ⟶ Smoothing.AffineLine :=
  RelativeBox.first F.parameter ≫ F.parameter

abbrev line : LineBundle (Square F) :=
  RelativeBox.line F.parameter (StandardConicDifferential.line F)

/-- The complete-square numerator of a times the canonical genus-zero
bivector in logarithmic frames. No denominator is used in this definition. -/
def numerator : AlgebraicSection (line F).sheaf :=
  RelativeBox.section F.parameter (coordinate F 1 0) (coordinate F 0 1) +
  RelativeBox.section F.parameter (coordinate F 0 1) (coordinate F 1 0) -
  sectionFromValue
    ((2 * (squareProjection F).appTop Smoothing.parameterFunction) •
      sectionValue (RelativeBox.section F.parameter
        (coordinate F 0 0) (coordinate F 0 0)))

/-- Scalarization of a tensor section by its actual two line frames. -/
theorem framedTensor {T : Scheme} {E G : OModule T}
    (e : E ≅ structureModule T) (g : G ≅ structureModule T)
    (s : AlgebraicSection E) (t : AlgebraicSection G) :
    tensorSection s t ≫
        ((tensorIso e g) ≪≫ TensorConstruction.leftUnitIso (structureModule T)).hom =
      scalarSection (sectionValue (s ≫ e.hom) * sectionValue (t ≫ g.hom)) := by
  change tensorSection s t ≫ tensorMap e.hom g.hom ≫
    (TensorConstruction.leftUnitIso (structureModule T)).hom = _
  rw [← Category.assoc, tensorSection_map]
  conv_lhs => rw [← sectionFromValue_sectionValue (s ≫ e.hom),
    ← sectionFromValue_sectionValue (t ≫ g.hom)]
  exact tensorScalarSection _ _

def testFrame {T : Scheme} (f : T ⟶ Square F)
    (e : pullbackModule (f ≫ RelativeBox.first F.parameter)
      (StandardConicDifferential.line F).sheaf ≅ structureModule T)
    (g : pullbackModule (f ≫ RelativeBox.second F.parameter)
      (StandardConicDifferential.line F).sheaf ≅ structureModule T) :
    pullbackModule f (line F).sheaf ≅ structureModule T :=
  RelativeBox.pullIso F.parameter f (StandardConicDifferential.line F) ≪≫
    tensorIso e g ≪≫ TensorConstruction.leftUnitIso (structureModule T)

def firstCoefficient {T : Scheme} (f : T ⟶ Square F)
    (e : pullbackModule (f ≫ RelativeBox.first F.parameter)
      (StandardConicDifferential.line F).sheaf ≅ structureModule T) (i j : Fin 2) : RingSections T ⊤ :=
  sectionValue (pullSection (f ≫ RelativeBox.first F.parameter)
    (coordinate F i j) ≫ e.hom)

def secondCoefficient {T : Scheme} (f : T ⟶ Square F)
    (g : pullbackModule (f ≫ RelativeBox.second F.parameter)
      (StandardConicDifferential.line F).sheaf ≅ structureModule T) (i j : Fin 2) : RingSections T ⊤ :=
  sectionValue (pullSection (f ≫ RelativeBox.second F.parameter)
    (coordinate F i j) ≫ g.hom)

theorem testFrame_box {T : Scheme} (f : T ⟶ Square F)
    (e : pullbackModule (f ≫ RelativeBox.first F.parameter)
      (StandardConicDifferential.line F).sheaf ≅ structureModule T)
    (g : pullbackModule (f ≫ RelativeBox.second F.parameter)
      (StandardConicDifferential.line F).sheaf ≅ structureModule T)
    (i j k l : Fin 2) :
    pullSection f (RelativeBox.section F.parameter
        (coordinate F i j) (coordinate F k l)) ≫
      (testFrame F f e g).hom =
        scalarSection (firstCoefficient F f e i j * secondCoefficient F f g k l) := by
  change (pullSection f _ ≫ (RelativeBox.pullIso _ _ _).hom) ≫
    ((tensorIso e g) ≪≫ TensorConstruction.leftUnitIso (structureModule T)).hom = _
  rw [RelativeBox.pullIso_section]
  exact framedTensor e g _ _

/-- Exact coefficient of the global numerator on any test scheme.
The scalar is pulled through the actual base map of the square. -/
theorem testFrame_numerator {T : Scheme} (f : T ⟶ Square F)
    (e : pullbackModule (f ≫ RelativeBox.first F.parameter)
      (StandardConicDifferential.line F).sheaf ≅ structureModule T)
    (g : pullbackModule (f ≫ RelativeBox.second F.parameter)
      (StandardConicDifferential.line F).sheaf ≅ structureModule T) :
    pullSection f (numerator F) ≫ (testFrame F f e g).hom =
      scalarSection
        (firstCoefficient F f e 1 0 * secondCoefficient F f g 0 1 +
          firstCoefficient F f e 0 1 * secondCoefficient F f g 1 0 -
          (2 * (f ≫ squareProjection F).appTop Smoothing.parameterFunction) *
            (firstCoefficient F f e 0 0 * secondCoefficient F f g 0 0)) := by
  have hadd {G : OModule (Square F)} (s t : AlgebraicSection G) :
      pullSection f (s + t) = pullSection f s + pullSection f t := by
    simp only [pullSection, restrictSection, Functor.map_add, Preadditive.comp_add]
  rw [numerator, Normalization.pullSection_sub, hadd,
    Preadditive.sub_comp, Preadditive.add_comp,
    testFrame_box, testFrame_box, Smoothing.StandardSourceProof.pullSection_scalar,
    Smoothing.StandardSourceProof.scalarSection_comp, testFrame_box]
  apply (sectionValue_bijective (structureModule T)).injective
  simp only [sub_eq_add_neg, sectionValue_add, sectionValue_neg, sectionValue_comp,
    scalarSection, sectionFromValue_spec, map_sub, map_add, map_mul,
    map_ofNat, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, smul_eq_mul]
  rfl

/-- On the two node frames, the global section has the literal
coefficient u*v' + v*u' - 2*a. -/
theorem testFrame_node {T : Scheme} (f : T ⟶ Square F)
    (e : pullbackModule (f ≫ RelativeBox.first F.parameter)
      (StandardConicDifferential.line F).sheaf ≅ structureModule T)
    (g : pullbackModule (f ≫ RelativeBox.second F.parameter)
      (StandardConicDifferential.line F).sheaf ≅ structureModule T)
    (he : firstCoefficient F f e 0 0 = 1)
    (hg : secondCoefficient F f g 0 0 = 1) :
    pullSection f (numerator F) ≫ (testFrame F f e g).hom =
      scalarSection
        (firstCoefficient F f e 1 0 * secondCoefficient F f g 0 1 +
          firstCoefficient F f e 0 1 * secondCoefficient F f g 1 0 -
          2 * (f ≫ squareProjection F).appTop Smoothing.parameterFunction) := by
  rw [testFrame_numerator, he, hg, one_mul, mul_one]

end Numerator

end LeBrunSalamon.Construction.StandardConicDifferential

/-- Classical hypersurface fundamental-class/adjunction corollary of
Stacks Project, Lemmas 48.29.1 and 48.29.2 (Tags 0E9Y and 0E9Z), with
the actual O(1,1) quotient-coordinate frames. This is a source-only
cotangent statement; its node and outer signs fix the normalization. -/
theorem LeBrunSalamon.PublishedInputs.Step3f.standardConic_fundamentalClass_exists
    (F : LeBrunSalamon.Construction.Smoothing.StandardSource) :
    ∃ q : LeBrunSalamon.PhaseTwentyFive.cotangentSheaf F.parameter ⟶
      LeBrunSalamon.PhaseTwentyFive.dualSheaf
        (LeBrunSalamon.Construction.StandardConicDifferential.line F).sheaf,
      ∀ (k : Fin 3) (i : Fin 2),
        LeBrunSalamon.Construction.StandardConicDifferential.chartCoefficient F q k i =
          LeBrunSalamon.Construction.StandardConicDifferential.chartLogValue k i := by
  sorry

/-- Project-facing alias of the reviewed hypersurface fundamental-class theorem. -/
theorem LeBrunSalamon.StandardInputs.standardConic_fundamentalClass_exists
    (F : LeBrunSalamon.Construction.Smoothing.StandardSource) :
    ∃ q : LeBrunSalamon.PhaseTwentyFive.cotangentSheaf F.parameter ⟶
      LeBrunSalamon.PhaseTwentyFive.dualSheaf
        (LeBrunSalamon.Construction.StandardConicDifferential.line F).sheaf,
      ∀ (k : Fin 3) (i : Fin 2),
        LeBrunSalamon.Construction.StandardConicDifferential.chartCoefficient F q k i =
          LeBrunSalamon.Construction.StandardConicDifferential.chartLogValue k i := by
  exact LeBrunSalamon.PublishedInputs.Step3f.standardConic_fundamentalClass_exists F

namespace LeBrunSalamon.Construction.StandardConicDifferential

variable (F : Smoothing.StandardSource)

/-- The reviewed source fundamental-class map in the fixed quotient-coordinate frames. -/
def fundamentalClass : cotangentSheaf F.parameter ⟶ dualSheaf (line F).sheaf :=
  Classical.choose (LeBrunSalamon.StandardInputs.standardConic_fundamentalClass_exists F)

theorem fundamentalClass_chartCoefficient (k : Fin 3) (i : Fin 2) :
    chartCoefficient F (fundamentalClass F) k i = chartLogValue k i :=
  Classical.choose_spec (LeBrunSalamon.StandardInputs.standardConic_fundamentalClass_exists F) k i

/-- The actual global logarithmic tangent morphism. -/
def logMap : (line F).sheaf ⟶ tangentSheaf F.parameter :=
  logMapFrom F (fundamentalClass F)

theorem logMap_evaluate (U : F.source.Opens) (m : SectionsOn (line F).sheaf U)
    (w : SectionsOn (cotangentSheaf F.parameter) U) :
    (dualEvaluation (cotangentSheaf F.parameter)).apply U ((logMap F).app U m) w =
      (dualEvaluation (line F).sheaf).apply U ((fundamentalClass F).app U w) m :=
  logMapFrom_evaluate F (fundamentalClass F) U m w

/-- Restriction of the global logarithmic map through the canonical
dual/cotangent comparisons of the actual source open immersion. -/
def chartLogMap (k : Fin 3) :
    pullbackModule (Smoothing.SourceAffineCharts.modelMap F k) (line F).sheaf ⟶
      tangentSheaf (Smoothing.SourceAffineCharts.modelMap F k ≫ F.parameter) :=
  (Scheme.Modules.pullback (Smoothing.SourceAffineCharts.modelMap F k)).map (logMap F) ≫
    dualBaseChange (Smoothing.SourceAffineCharts.modelMap F k) (cotangentSheaf F.parameter) ≫
      ContactDerivativeIsoProof.dualMap (chartCotangentIso F k).inv

theorem chartLogMap_eq_transpose (k : Fin 3) :
    chartLogMap F k = transpose (chartForm F (fundamentalClass F) k) := by
  change (Scheme.Modules.pullback (Smoothing.SourceAffineCharts.modelMap F k)).map
      (transpose (fundamentalClass F)) ≫
    dualBaseChange (Smoothing.SourceAffineCharts.modelMap F k) (cotangentSheaf F.parameter) ≫
      ContactDerivativeIsoProof.dualMap (chartCotangentIso F k).inv =
    transpose ((chartCotangentIso F k).inv ≫
      (Scheme.Modules.pullback (Smoothing.SourceAffineCharts.modelMap F k)).map
        (fundamentalClass F) ≫
      dualBaseChange (Smoothing.SourceAffineCharts.modelMap F k) (line F).sheaf)
  rw [transpose_comp, ← transpose_pullback, Category.assoc]

/-- The global logarithmic map acts on the actual affine coordinates
with exactly the reviewed node and outer coefficients. -/
theorem chartLogMap_coordinate (k : Fin 3) (i : Fin 2) :
    tangentActs (Smoothing.SourceAffineCharts.modelMap F k ≫ F.parameter) ⊤
      ((chartLogMap F k).app ⊤ (sectionValue (chartLineFrame F k).inv))
      (Smoothing.SourceAffineCharts.planeFunction (MvPolynomial.X i)) =
        chartLogValue k i := by
  rw [chartLogMap_eq_transpose]
  change (dualEvaluation (cotangentSheaf
    (Smoothing.SourceAffineCharts.modelMap F k ≫ F.parameter))).apply ⊤
      ((transpose (chartForm F (fundamentalClass F) k)).app ⊤
        (sectionValue (chartLineFrame F k).inv))
      ((cotangentPresentation
        (Smoothing.SourceAffineCharts.modelMap F k ≫ F.parameter)).differential.apply ⊤
        (Smoothing.SourceAffineCharts.planeFunction (MvPolynomial.X i))) = _
  rw [transpose_evaluate]
  exact fundamentalClass_chartCoefficient F k i

end LeBrunSalamon.Construction.StandardConicDifferential

end
