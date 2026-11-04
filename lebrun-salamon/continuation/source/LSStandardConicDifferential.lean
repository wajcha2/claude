import LSNodalFixedEnds
import LSStandardConicFrames
import LSConicFundamentalClassConstruction

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
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseSeven LeBrunSalamon.PhaseTwentyFive
open LeBrunSalamon.PhaseTwentySix LeBrunSalamon.PhaseTwentySeven
open LeBrunSalamon.PhaseTwentyEight LeBrunSalamon.PhaseTwentyNine
open LeBrunSalamon.PhaseThirty LeBrunSalamon.PhaseThirtyTwo
open LeBrunSalamon.PhaseThirtyFour LeBrunSalamon.Skeleton

open LeBrunSalamon.Refinement

namespace LeBrunSalamon.Construction.TraitContact

namespace RelativeBox

variable {S B : Scheme} (pi : S ⟶ B)

abbrev Square := pullback pi pi

abbrev first : Square pi ⟶ S := pullback.fst pi pi
abbrev second : Square pi ⟶ S := pullback.snd pi pi

def line (L : LineBundle S) : LineBundle (Square pi) :=
  tensorLine (pullbackLine (first pi) L) (pullbackLine (second pi) L)

def «section» {L : LineBundle S} (a b : AlgebraicSection L.sheaf) :
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
    pullSection f («section» pi a b) ≫ (pullIso pi f L).hom =
      tensorSection (pullSection (f ≫ first pi) a)
        (pullSection (f ≫ second pi) b) := by
  letI := tensorPullbackComparison_isIso f
    (pullbackModule (first pi) L.sheaf) (pullbackModule (second pi) L.sheaf)
  rw [«section», ← tensorPullbackComparison_onSections]
  change (tensorSection _ _ ≫ tensorPullbackComparison f
    (pullbackModule (first pi) L.sheaf) (pullbackModule (second pi) L.sheaf)) ≫ _ = _
  simp only [pullIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
    Category.assoc, IsIso.hom_inv_id_assoc]
  change tensorSection _ _ ≫ tensorMap _ _ = _
  rw [tensorSection_map, compositionPullback_sections, compositionPullback_sections]

end RelativeBox

end LeBrunSalamon.Construction.TraitContact

namespace LeBrunSalamon.Construction.StandardConicDifferential

open Smoothing Smoothing.CoordinateCharts Smoothing.SourceAffineCharts

variable (F : StandardSource)

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
  RelativeBox.«section» F.parameter (coordinate F 1 0) (coordinate F 0 1) +
  RelativeBox.«section» F.parameter (coordinate F 0 1) (coordinate F 1 0) -
  sectionFromValue
    ((2 * (squareProjection F).appTop Smoothing.parameterFunction) •
      sectionValue (RelativeBox.«section» F.parameter
        (coordinate F 0 0) (coordinate F 0 0)))

/-- Scalar value with its ring-valued codomain made explicit. -/
def scalarValue {T : Scheme} (s : AlgebraicSection (structureModule T)) :
    RingSections T ⊤ := sectionValue s

/-- Scalarization of a tensor section by its actual two line frames. -/
theorem framedTensor {T : Scheme} {E G : OModule T}
    (e : E ≅ structureModule T) (g : G ≅ structureModule T)
    (s : AlgebraicSection E) (t : AlgebraicSection G) :
    tensorSection s t ≫
        ((tensorIso e g) ≪≫ TensorConstruction.leftUnitIso (structureModule T)).hom =
      scalarSection (scalarValue (s ≫ e.hom) * scalarValue (t ≫ g.hom)) := by
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
    pullSection f (RelativeBox.«section» F.parameter
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
  rw [numerator, Normalization.BundleGluing.pullSection_sub, hadd,
    Preadditive.sub_comp, Preadditive.add_comp,
    testFrame_box, testFrame_box, Smoothing.StandardSourceProof.pullSection_scalar,
    Smoothing.StandardSourceProof.scalarSection_comp, testFrame_box]
  apply (sectionValue_bijective (structureModule T)).injective
  simp only [sub_eq_add_neg, sectionValue_add, sectionValue_neg, sectionValue_comp,
    scalarSection, sectionFromValue_spec, map_sub, map_add, map_mul,
    map_ofNat, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, smul_eq_mul]

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

/-- The original three prescribed cotangent formulas glue through the
actual homogeneous line frames. The composite source claim is proved;
its historical declaration name is retained for downstream compatibility. -/
theorem LeBrunSalamon.PublishedInputs.Step3f.standardConic_fundamentalClass_exists
    (F : LeBrunSalamon.Construction.Smoothing.StandardSource) :
    ∃ q : LeBrunSalamon.PhaseTwentyFive.cotangentSheaf F.parameter ⟶
      LeBrunSalamon.PhaseTwentyFive.dualSheaf
        (LeBrunSalamon.Construction.StandardConicDifferential.line F).sheaf,
      ∀ (k : Fin 3) (i : Fin 2),
        LeBrunSalamon.Construction.StandardConicDifferential.chartCoefficient F q k i =
          LeBrunSalamon.Construction.StandardConicDifferential.chartLogValue k i := by
  exact LeBrunSalamon.Construction.StandardConicConstruction.fundamentalClass_exists F

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
