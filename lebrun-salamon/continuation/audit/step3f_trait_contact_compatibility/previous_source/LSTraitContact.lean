import LSFormalTraitModel
import LSStandardConicDifferential
import LSRelativeDifferential

/-!
# Contact cancellation on the actual nodal conic over C[[t]]

The ordinary calculations in this file use the actual line O(1,1), its
homogeneous coordinate sections, and the logarithmic derivation of uv=a.
The numerator is a global section on the complete relative square.
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
open LeBrunSalamon.Refinement

namespace LeBrunSalamon.Construction.TraitContact

namespace LineEndomorphisms

open LocalFrames

/-- The scalar of a rank-one endomorphism is an actual global function.
Its local coefficients glue because frame transition units cancel. -/
theorem scalar_existsUnique {Y : Scheme} (L : LineBundle Y)
    (f : L.sheaf ⟶ L.sheaf) :
    ∃! a : RingSections Y ⊤, f = GlobalScalars.scalarEnd L.sheaf a := by
  classical
  obtain ⟨q, hq, hr⟩ := L.locallyFree
  letI := hq
  have hcover : (⨆ i : q.I, q.X i) = ⊤ :=
    (_root_.Opens.coversTop_iff Y q.X).mp q.coversTop
  let e (i : q.I) : OverFrame L.sheaf (q.X i) :=
    (coproductUniqueIso
      (fun _ : Fin 1 => SheafOfModules.unit (Y.ringCatSheaf.over (q.X i)))).symm ≪≫
        SheafTensor.localBasisTrivialization q hr i
  let c (i : q.I) : RingSections Y (q.X i) := mapCoefficient (e i) (e i) f
  have hc : TopCat.Presheaf.IsCompatible (structureModule Y).presheaf q.X c := by
    intro i j
    change Y.presheaf.map (homOfLE inf_le_left).op (c i) =
      Y.presheaf.map (homOfLE inf_le_right).op (c j)
    dsimp only [c]
    rw [mapCoefficient_restrict, mapCoefficient_restrict]
    exact endCoefficient_frame_independent _ _ f
  obtain ⟨a, ha, _⟩ :=
    (TwoChartSections.sectionSheaf (structureModule Y)).existsUnique_gluing'
      q.X ⊤ (fun i => homOfLE (show q.X i ≤ ⊤ from le_top))
      (by rw [hcover]) c hc
  have hf : f = GlobalScalars.scalarEnd L.sheaf a := by
    apply P1Ideal.hom_ext_of_localSections q.X hcover
    intro i
    apply localHom_eq_of_mapCoefficient_eq (e i) (e i)
    rw [mapCoefficient_scalarEnd]
    exact (ha i).symm
  refine ⟨a, hf, ?_⟩
  intro b hb
  apply (TwoChartSections.sectionSheaf (structureModule Y)).eq_of_locally_eq'
    q.X ⊤ (fun i => homOfLE (show q.X i ≤ ⊤ from le_top)) (by rw [hcover])
  intro i
  have h := congrArg (mapCoefficient (e i) (e i)) (hb.symm.trans hf)
  simpa only [mapCoefficient_scalarEnd] using h

/-- A map between two identified actual line bundles is multiplication
by a unique regular function followed by the given identification. -/
theorem hom_scalar_existsUnique {Y : Scheme} (L M : LineBundle Y)
    (e : L.sheaf ≅ M.sheaf) (f : L.sheaf ⟶ M.sheaf) :
    ∃! a : RingSections Y ⊤,
      f = GlobalScalars.scalarEnd L.sheaf a ≫ e.hom := by
  obtain ⟨a, ha, hu⟩ := scalar_existsUnique L (f ≫ e.inv)
  refine ⟨a, ?_, ?_⟩
  · apply (cancel_mono e.inv).mp
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using ha
  · intro b hb
    apply hu b
    rw [hb, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- When the canonical pullback on functions is bijective, the scalar
comes from the actual base, with no choice of a different coefficient map. -/
theorem hom_baseScalar_existsUnique {Y B : Scheme} (pi : Y ⟶ B)
    (hpi : Function.Bijective pi.appTop) (L M : LineBundle Y)
    (e : L.sheaf ≅ M.sheaf) (f : L.sheaf ⟶ M.sheaf) :
    ∃! a : RingSections B ⊤,
      f = GlobalScalars.scalarEnd L.sheaf (pi.appTop a) ≫ e.hom := by
  obtain ⟨r, hr, hu⟩ := hom_scalar_existsUnique L M e f
  obtain ⟨a, ha⟩ := hpi.surjective r
  refine ⟨a, by simpa only [ha] using hr, ?_⟩
  intro b hb
  apply hpi.injective
  exact (hu _ hb).trans ha.symm

theorem scalarEnd_eq_zero_iff {Y : Scheme} (L : LineBundle Y)
    (a : RingSections Y ⊤) : GlobalScalars.scalarEnd L.sheaf a = 0 ↔ a = 0 := by
  constructor
  · intro ha
    obtain ⟨b, hb, hu⟩ := scalar_existsUnique L (0 : L.sheaf ⟶ L.sheaf)
    exact (hu a ha.symm).trans
      (hu 0 (GlobalScalars.scalarEnd_zero L.sheaf).symm).symm
  · rintro rfl
    exact GlobalScalars.scalarEnd_zero L.sheaf

/-- Pulling a scalar endomorphism uses the actual pullback of its
coefficient. This includes nilpotent coefficients on the test scheme. -/
theorem scalarEnd_pullback {Y Z : Scheme} (f : Y ⟶ Z)
    (E : OModule Z) (a : RingSections Z ⊤) :
    (Scheme.Modules.pullback f).map (GlobalScalars.scalarEnd E a) =
      GlobalScalars.scalarEnd (pullbackModule f E) (f.appTop a) := by
  apply PullbackPairProof.pullbackHom_ext
  intro U e
  rw [ExternalExchangeCoherenceProof.pullLocalSection_map,
    GlobalScalars.scalarEnd_app, PullbackPairProof.pullLocalSection_smul,
    GlobalScalars.scalarEnd_app]
  congr 1
  exact congrArg (fun k : Z.presheaf.obj (Opposite.op ⊤) ⟶
    Y.presheaf.obj (Opposite.op (f ⁻¹ᵁ U)) => k a)
      (f.naturality (homOfLE (show U ≤ ⊤ from le_top)).op)

/-- A vanishing pulled line morphism detects the actual base scalar. -/
theorem baseScalar_zero_of_pullback_zero {Y B T : Scheme} (pi : Y ⟶ B)
    (L M : LineBundle Y) (e : L.sheaf ≅ M.sheaf)
    (a : RingSections B ⊤) (f : L.sheaf ⟶ M.sheaf)
    (hf : f = GlobalScalars.scalarEnd L.sheaf (pi.appTop a) ≫ e.hom)
    (j : T ⟶ Y) (hj : (Scheme.Modules.pullback j).map f = 0) :
    (j ≫ pi).appTop a = 0 := by
  have hs : GlobalScalars.scalarEnd (pullbackModule j L.sheaf)
      (j.appTop (pi.appTop a)) = 0 := by
    apply (cancel_mono ((Scheme.Modules.pullback j).mapIso e).hom).mp
    rw [← scalarEnd_pullback, ← Functor.map_comp, ← hf, hj, zero_comp]
  exact (scalarEnd_eq_zero_iff (pullbackLine j L) _).mp hs

end LineEndomorphisms

namespace PullbackZero

/-- Zero is transported through the actual composition comparison. -/
theorem composite {T Y Z : Scheme} (f : T ⟶ Y) (g : Y ⟶ Z)
    {E M : OModule Z} (q : E ⟶ M)
    (hq : (Scheme.Modules.pullback g).map q = 0) :
    (Scheme.Modules.pullback (f ≫ g)).map q = 0 := by
  apply (cancel_epi (compositionPullback f g (f ≫ g) rfl E).hom).mp
  rw [← Normalization.BundleGluing.compositionPullback_naturality,
    hq, Functor.map_zero, zero_comp, comp_zero]

theorem iterated {T Y Z : Scheme} (f : T ⟶ Y) (g : Y ⟶ Z)
    (k : T ⟶ Z) (hk : f ≫ g = k) {E M : OModule Z} (q : E ⟶ M)
    (hq : (Scheme.Modules.pullback k).map q = 0) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map q) = 0 := by
  apply (cancel_mono (compositionPullback f g k hk M).hom).mp
  rw [Normalization.BundleGluing.compositionPullback_naturality,
    hq, comp_zero, zero_comp]

end PullbackZero

namespace LogarithmicSource

open StableMaps.FormalArcs
open StandardConicDifferential

variable (F : Smoothing.StandardSource) (a : Coefficients)

abbrev toUniversal : Model F a ⟶ F.source :=
  pullback.fst F.parameter (parameterMap a)

/-- The model O(1,1) is the actual pullback of the universal O(1,1),
through the same tensor and composition comparisons used by its sections. -/
def lineComparison :
    pullbackModule (toUniversal F a) (StandardConicDifferential.line F).sheaf ≅
      (modelLine F a).sheaf := by
  let f := toUniversal F a
  let H := (projectiveCoordinates 1).hyperplane.sheaf
  letI := tensorPullbackComparison_isIso f
    (pullbackModule F.left H) (pullbackModule F.right H)
  exact (asIso (tensorPullbackComparison f
    (pullbackModule F.left H) (pullbackModule F.right H))).symm ≪≫
      tensorIso
        (compositionPullback f F.left (modelLeft F a) rfl H)
        (compositionPullback f F.right (modelRight F a) rfl H)

def cotangentComparison :
    pullbackModule (toUniversal F a) (cotangentSheaf F.parameter) ≅
      cotangentSheaf (modelProjection F a) := by
  letI := LeBrunSalamon.StandardInputs.cotangentPullback_isIso
    F.parameter (parameterMap a)
  exact asIso (CotangentBaseChange.canonicalMap F.parameter (parameterMap a))

/-- Arbitrary base change of the actual source fundamental class. The
relative cotangent comparison is canonical, including at the node. -/
def fundamentalClass : cotangentSheaf (modelProjection F a) ⟶
    dualSheaf (modelLine F a).sheaf :=
  (cotangentComparison F a).inv ≫
    (Scheme.Modules.pullback (toUniversal F a)).map
      (StandardConicDifferential.fundamentalClass F) ≫
    dualBaseChange (toUniversal F a) (StandardConicDifferential.line F).sheaf ≫
    ContactDerivativeIsoProof.dualMap (lineComparison F a).inv

def logMap : (modelLine F a).sheaf ⟶ tangentSheaf (modelProjection F a) :=
  transpose (fundamentalClass F a)

/-- The logarithmic map is the base change of the universal one, with
the exact dual and relative-cotangent comparisons retained. -/
theorem logMap_baseChange :
    logMap F a = (lineComparison F a).inv ≫
      (Scheme.Modules.pullback (toUniversal F a)).map
        (StandardConicDifferential.logMap F) ≫
      dualBaseChange (toUniversal F a) (cotangentSheaf F.parameter) ≫
      ContactDerivativeIsoProof.dualMap (cotangentComparison F a).inv := by
  unfold logMap fundamentalClass
  rw [transpose_comp, transpose_dualMap, ← transpose_pullback]
  rfl

variable {d : ℕ} (X : SmoothProperComplexVariety d)
    (e : Model F a ⟶ X.scheme)
    (he : e ≫ X.structureMap = modelProjection F a ≫ toC)

def targetCotangent : pullbackModule e (cotangentSheaf X.structureMap) ⟶
    cotangentSheaf (modelProjection F a) :=
  RelativeDifferential.cotangent (modelProjection F a) X.structureMap e toC he

/-- Actual relative differentiation into the smooth target, dual to its
canonical relative cotangent map. The source need not be smooth. -/
def differential : tangentSheaf (modelProjection F a) ⟶
    pullbackModule e (tangentSheaf X.structureMap) := by
  letI := dualBaseChange_isIso e (smooth_cotangent_rank X.structureMap d X.smooth)
  exact ContactDerivativeIsoProof.dualMap (targetCotangent F a X e he) ≫
    (asIso (dualBaseChange e (cotangentSheaf X.structureMap))).inv

/-- The regular target-valued logarithmic velocity is obtained by
transposing the actual target cotangent map followed by the source map. -/
def velocity : (modelLine F a).sheaf ⟶
    pullbackModule e (tangentSheaf X.structureMap) := by
  letI := dualBaseChange_isIso e (smooth_cotangent_rank X.structureMap d X.smooth)
  exact transpose (targetCotangent F a X e he ≫ fundamentalClass F a) ≫
    (asIso (dualBaseChange e (cotangentSheaf X.structureMap))).inv

theorem velocity_eq : velocity F a X e he =
    logMap F a ≫ differential F a X e he := by
  letI := dualBaseChange_isIso e (smooth_cotangent_rank X.structureMap d X.smooth)
  unfold velocity logMap differential
  rw [transpose_comp, Category.assoc]

theorem velocity_normalized :
    velocity F a X e he ≫ dualBaseChange e (cotangentSheaf X.structureMap) =
      transpose (targetCotangent F a X e he ≫ fundamentalClass F a) := by
  letI := dualBaseChange_isIso e (smooth_cotangent_rank X.structureMap d X.smooth)
  simp only [velocity, Category.assoc, asIso_inv, IsIso.inv_hom_id, Category.comp_id]

/-- Vanishing of the pulled source cotangent map implies vanishing of
the pulled actual target velocity. Only the target cotangent bundle is
used as locally free; no such claim is made at the source node. -/
theorem velocity_pullback_zero {T : Scheme} (j : T ⟶ Model F a)
    (hj : (Scheme.Modules.pullback j).map (fundamentalClass F a) = 0) :
    (Scheme.Modules.pullback j).map (velocity F a X e he) = 0 := by
  let Ω := cotangentSheaf X.structureMap
  have hΩ := smooth_cotangent_rank X.structureMap d X.smooth
  letI := dualBaseChange_isIso e hΩ
  letI := dualBaseChange_isIso j (pullback_locallyFree e hΩ)
  apply (cancel_mono ((Scheme.Modules.pullback j).map
    (dualBaseChange e Ω) ≫ dualBaseChange j (pullbackModule e Ω))).mp
  rw [zero_comp, ← Category.assoc, ← Functor.map_comp, velocity_normalized,
    transpose_pullback, Functor.map_comp, hj, comp_zero, zero_comp,
    transpose_zero]

end LogarithmicSource

namespace ContactScalar

open StableMaps.FormalArcs

variable {n : ℕ} (X : ContactFanoManifold n)
    (F : Smoothing.StandardSource) (a : Coefficients)
    (e : Model F a ⟶ X.variety.scheme)
    (he : e ≫ X.variety.structureMap = modelProjection F a ≫ toC)

def morphism : (modelLine F a).sheaf ⟶ pullbackModule e X.contact.sequence.line.sheaf :=
  LogarithmicSource.velocity F a X.variety e he ≫
    (Scheme.Modules.pullback e).map X.contact.sequence.form

/-- The contact coefficient is an actual power series on the base. It
is obtained from the canonical map on global functions and a genuine
isomorphism of the two line bundles. -/
theorem existsUnique
    (hfunctions : Function.Bijective (modelProjection F a).appTop)
    (ell : (modelLine F a).sheaf ≅ pullbackModule e X.contact.sequence.line.sheaf) :
    ∃! h : Coefficients, morphism X F a e he =
      GlobalScalars.scalarEnd (modelLine F a).sheaf
        ((modelProjection F a).appTop (coefficientSection h)) ≫ ell.hom := by
  obtain ⟨r, hr, hu⟩ := LineEndomorphisms.hom_baseScalar_existsUnique
    (modelProjection F a) hfunctions (modelLine F a)
    (pullbackLine e X.contact.sequence.line) ell (morphism X F a e he)
  let h := (Scheme.ΓSpecIso (CommRingCat.of Coefficients)).hom r
  have hh : coefficientSection h = r :=
    Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of Coefficients)) r
  refine ⟨h, by simpa only [hh] using hr, ?_⟩
  intro k hk
  apply (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of Coefficients)).inv).injective
  change coefficientSection k = coefficientSection h
  exact (hu _ hk).trans hh.symm

theorem pullback_zero_of_source_zero {T : Scheme} (j : T ⟶ Model F a)
    (hj : (Scheme.Modules.pullback j).map
      (LogarithmicSource.fundamentalClass F a) = 0) :
    (Scheme.Modules.pullback j).map (morphism X F a e he) = 0 := by
  rw [morphism, Functor.map_comp,
    LogarithmicSource.velocity_pullback_zero F a X.variety e he j hj, zero_comp]

end ContactScalar

namespace ThickenedNode

open StableMaps.FormalArcs

abbrev Ring (a : Coefficients) := Coefficients ⧸ Ideal.span {a}
abbrev Space (a : Coefficients) : Scheme := Spec (CommRingCat.of (Ring a))

/-- The entire infinitesimal base on which the smoothing element
vanishes. This retains the full order of a, including its unit factor. -/
def toBase (a : Coefficients) : Space a ⟶ Trait :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a})))

def toComplex (a : Coefficients) : Space a ⟶ ComplexBase := toBase a ≫ toC

theorem toBase_coefficient (a h : Coefficients) :
    (toBase a).appTop (coefficientSection h) =
      (Scheme.ΓSpecIso (CommRingCat.of (Ring a))).inv
        (Ideal.Quotient.mk (Ideal.span {a}) h) := by
  exact (congrArg (fun k : CommRingCat.of Coefficients ⟶
    (Space a).presheaf.obj (Opposite.op ⊤) => k h)
      (Scheme.ΓSpecIso_inv_naturality
        (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a}))))).symm

theorem toBase_coefficient_zero_iff (a h : Coefficients) :
    (toBase a).appTop (coefficientSection h) = 0 ↔ a ∣ h := by
  rw [toBase_coefficient]
  have hz : (Scheme.ΓSpecIso (CommRingCat.of (Ring a))).inv
      (Ideal.Quotient.mk (Ideal.span {a}) h) = 0 ↔
      Ideal.Quotient.mk (Ideal.span {a}) h = 0 := by
    constructor
    · intro he
      apply (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of (Ring a))).inv).injective
      simpa only [map_zero] using he
    · rintro he
      rw [he, map_zero]
  rw [hz, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

theorem parameter_zero (a : Coefficients) :
    toBase a ≫ parameterMap a = toComplex a ≫ Smoothing.scalarPoint 0 := by
  apply Smoothing.CoordinateCharts.functionMap_ext (toComplex a)
  · rw [Category.assoc, parameterMap_toC]
    rfl
  · rw [Category.assoc, Smoothing.scalarPoint_overC, Category.comp_id]
  · change (toBase a).appTop ((parameterMap a).appTop Smoothing.parameterFunction) =
      (toComplex a).appTop ((Smoothing.scalarPoint 0).appTop Smoothing.parameterFunction)
    rw [parameterMap_parameter, Smoothing.SourceMarksProof.scalarPoint_zero_parameter,
      map_zero]
    exact (toBase_coefficient_zero_iff a a).mpr (dvd_refl a)

variable (F : Smoothing.StandardSource) (a : Coefficients)
    (node : ComplexBase ⟶ F.source)
    (hnode : node ≫ F.parameter = Smoothing.scalarPoint 0)

def point : Space a ⟶ Model F a :=
  pullback.lift (toComplex a ≫ node) (toBase a)
    (by rw [Category.assoc, hnode, parameter_zero])

@[reassoc] theorem point_projection :
    point F a node hnode ≫ modelProjection F a = toBase a :=
  pullback.lift_snd _ _ _

@[reassoc] theorem point_universal :
    point F a node hnode ≫ LogarithmicSource.toUniversal F a = toComplex a ≫ node :=
  pullback.lift_fst _ _ _

/-- The base-changed fundamental class vanishes on the whole infinitesimal
node as soon as its universal node fibre vanishes. -/
theorem fundamentalClass_zero
    (hzero : (Scheme.Modules.pullback node).map
      (StandardConicDifferential.fundamentalClass F) = 0) :
    (Scheme.Modules.pullback (point F a node hnode)).map
      (LogarithmicSource.fundamentalClass F a) = 0 := by
  have hcomp := PullbackZero.composite (toComplex a) node
    (StandardConicDifferential.fundamentalClass F) hzero
  have hiter := PullbackZero.iterated (point F a node hnode)
    (LogarithmicSource.toUniversal F a) (toComplex a ≫ node)
    (point_universal F a node hnode)
    (StandardConicDifferential.fundamentalClass F) hcomp
  simp only [LogarithmicSource.fundamentalClass, Functor.map_comp, hiter,
    comp_zero, zero_comp]

include hnode in
/-- The actual contact scalar is divisible by the exact smoothing
element. Detection is on R/(a), so it retains every infinitesimal order. -/
theorem contact_coefficient_divisible {n : ℕ} (X : ContactFanoManifold n)
    (e : Model F a ⟶ X.variety.scheme)
    (he : e ≫ X.variety.structureMap = modelProjection F a ≫ toC)
    (ell : (modelLine F a).sheaf ≅ pullbackModule e X.contact.sequence.line.sheaf)
    (h : Coefficients)
    (hscalar : ContactScalar.morphism X F a e he =
      GlobalScalars.scalarEnd (modelLine F a).sheaf
        ((modelProjection F a).appTop (coefficientSection h)) ≫ ell.hom)
    (hzero : (Scheme.Modules.pullback node).map
      (StandardConicDifferential.fundamentalClass F) = 0) : a ∣ h := by
  have hj := ContactScalar.pullback_zero_of_source_zero X F a e he
    (point F a node hnode) (fundamentalClass_zero F a node hnode hzero)
  have hh := LineEndomorphisms.baseScalar_zero_of_pullback_zero
    (modelProjection F a) (modelLine F a) (pullbackLine e X.contact.sequence.line)
    ell (coefficientSection h) (ContactScalar.morphism X F a e he) hscalar
    (point F a node hnode) hj
  rw [point_projection] at hh
  exact (toBase_coefficient_zero_iff a h).mp hh

end ThickenedNode


namespace ModelNumerator

open StableMaps.FormalArcs
open Smoothing.CoordinateCharts Smoothing.SourceAffineCharts

variable (F : Smoothing.StandardSource) (a : Coefficients)

/-- All four sections use the same chosen projective quotient lines. -/
def coordinate (i j : Fin 2) : AlgebraicSection (modelLine F a).sheaf :=
  tensorSection
    (pullSection (modelLeft F a) ((projectiveCoordinates 1).coordinate i))
    (pullSection (modelRight F a) ((projectiveCoordinates 1).coordinate j))

abbrev Square := RelativeBox.Square (modelProjection F a)

abbrev squareProjection : Square F a ⟶ Trait :=
  RelativeBox.first (modelProjection F a) ≫ modelProjection F a

abbrev line : LineBundle (Square F a) :=
  RelativeBox.line (modelProjection F a) (modelLine F a)

/-- The complete-square numerator of a times the canonical genus-zero
bivector in logarithmic frames. No denominator is used in this definition. -/
def numerator : AlgebraicSection (line F a).sheaf :=
  RelativeBox.section (modelProjection F a) (coordinate F a 1 0) (coordinate F a 0 1) +
  RelativeBox.section (modelProjection F a) (coordinate F a 0 1) (coordinate F a 1 0) -
  sectionFromValue
    ((2 * (squareProjection F a).appTop (coefficientSection a)) •
      sectionValue (RelativeBox.section (modelProjection F a)
        (coordinate F a 0 0) (coordinate F a 0 0)))

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

def testFrame {T : Scheme} (f : T ⟶ Square F a)
    (e : pullbackModule (f ≫ RelativeBox.first (modelProjection F a))
      (modelLine F a).sheaf ≅ structureModule T)
    (g : pullbackModule (f ≫ RelativeBox.second (modelProjection F a))
      (modelLine F a).sheaf ≅ structureModule T) :
    pullbackModule f (line F a).sheaf ≅ structureModule T :=
  RelativeBox.pullIso (modelProjection F a) f (modelLine F a) ≪≫
    tensorIso e g ≪≫ TensorConstruction.leftUnitIso (structureModule T)

def firstCoefficient {T : Scheme} (f : T ⟶ Square F a)
    (e : pullbackModule (f ≫ RelativeBox.first (modelProjection F a))
      (modelLine F a).sheaf ≅ structureModule T) (i j : Fin 2) : RingSections T ⊤ :=
  sectionValue (pullSection (f ≫ RelativeBox.first (modelProjection F a))
    (coordinate F a i j) ≫ e.hom)

def secondCoefficient {T : Scheme} (f : T ⟶ Square F a)
    (g : pullbackModule (f ≫ RelativeBox.second (modelProjection F a))
      (modelLine F a).sheaf ≅ structureModule T) (i j : Fin 2) : RingSections T ⊤ :=
  sectionValue (pullSection (f ≫ RelativeBox.second (modelProjection F a))
    (coordinate F a i j) ≫ g.hom)

theorem testFrame_box {T : Scheme} (f : T ⟶ Square F a)
    (e : pullbackModule (f ≫ RelativeBox.first (modelProjection F a))
      (modelLine F a).sheaf ≅ structureModule T)
    (g : pullbackModule (f ≫ RelativeBox.second (modelProjection F a))
      (modelLine F a).sheaf ≅ structureModule T)
    (i j k l : Fin 2) :
    pullSection f (RelativeBox.section (modelProjection F a)
        (coordinate F a i j) (coordinate F a k l)) ≫
      (testFrame F a f e g).hom =
        scalarSection (firstCoefficient F a f e i j * secondCoefficient F a f g k l) := by
  change (pullSection f _ ≫ (RelativeBox.pullIso _ _ _).hom) ≫
    ((tensorIso e g) ≪≫ TensorConstruction.leftUnitIso (structureModule T)).hom = _
  rw [RelativeBox.pullIso_section]
  exact framedTensor e g _ _

/-- Exact coefficient of the global numerator on any test scheme.
The scalar is pulled through the actual base map of the square. -/
theorem testFrame_numerator {T : Scheme} (f : T ⟶ Square F a)
    (e : pullbackModule (f ≫ RelativeBox.first (modelProjection F a))
      (modelLine F a).sheaf ≅ structureModule T)
    (g : pullbackModule (f ≫ RelativeBox.second (modelProjection F a))
      (modelLine F a).sheaf ≅ structureModule T) :
    pullSection f (numerator F a) ≫ (testFrame F a f e g).hom =
      scalarSection
        (firstCoefficient F a f e 1 0 * secondCoefficient F a f g 0 1 +
          firstCoefficient F a f e 0 1 * secondCoefficient F a f g 1 0 -
          (2 * (f ≫ squareProjection F a).appTop (coefficientSection a)) *
            (firstCoefficient F a f e 0 0 * secondCoefficient F a f g 0 0)) := by
  have hadd {G : OModule (Square F a)} (s t : AlgebraicSection G) :
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
theorem testFrame_node {T : Scheme} (f : T ⟶ Square F a)
    (e : pullbackModule (f ≫ RelativeBox.first (modelProjection F a))
      (modelLine F a).sheaf ≅ structureModule T)
    (g : pullbackModule (f ≫ RelativeBox.second (modelProjection F a))
      (modelLine F a).sheaf ≅ structureModule T)
    (he : firstCoefficient F a f e 0 0 = 1)
    (hg : secondCoefficient F a f g 0 0 = 1) :
    pullSection f (numerator F a) ≫ (testFrame F a f e g).hom =
      scalarSection
        (firstCoefficient F a f e 1 0 * secondCoefficient F a f g 0 1 +
          firstCoefficient F a f e 0 1 * secondCoefficient F a f g 1 0 -
          2 * (f ≫ squareProjection F a).appTop (coefficientSection a)) := by
  rw [testFrame_numerator, he, hg, one_mul, mul_one]

end ModelNumerator

end LeBrunSalamon.Construction.TraitContact

end
