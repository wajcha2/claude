import LSTangentComparison

/-!
## The actual relative-Hom tangent comparison at the nodal map

The parameter directions below are the original affine point derivations.
Their lifts are actual maps from the dual-number spectrum. The full relative
Hom universal property is used on that nonreduced scheme, and the resulting
central-family deformation is normalized by the original epsilon.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.PhaseThirty LeBrunSalamon.Skeleton
open LeBrunSalamon.Construction

namespace LeBrunSalamon.Construction.StandardInputs.InfinitesimalGeometry

/-- The simply transitive action of cotangent functionals on first-order
lifts, based at the actual constant lift. Source: Stacks 04BU, Lemma 37.9.2,
04FJ, Lemma 37.9.5, and 04FK, Remark 37.9.6. The map here was constructed
from actual epsilon coefficients on every target open in LSHomVelocity;
its normalization on local differentials is already proved there. -/
theorem _root_.LeBrunSalamon.PublishedInputs.Step3f.firstOrder_cotangentHom_bijective
    {Y X : Scheme}
    (sY : Y ⟶ ComplexBase) (sX : X ⟶ ComplexBase)
    (f : Y ⟶ X) (hf : f ≫ sX = sY) :
    Function.Bijective (fun D : Lines.FamilyVariation.Deformation sY sX f =>
      D.cotangentHom) := by
  sorry

/-- Project-facing alias of the cotangent torsor theorem for first-order lifts. -/
theorem firstOrder_cotangentHom_bijective {Y X : Scheme}
    (sY : Y ⟶ ComplexBase) (sX : X ⟶ ComplexBase)
    (f : Y ⟶ X) (hf : f ≫ sX = sY) :
    Function.Bijective (fun D : Lines.FamilyVariation.Deformation sY sX f =>
      D.cotangentHom) := by
  exact LeBrunSalamon.PublishedInputs.Step3f.firstOrder_cotangentHom_bijective
    sY sX f hf

end LeBrunSalamon.Construction.StandardInputs.InfinitesimalGeometry

namespace LeBrunSalamon.Construction.Normalization.NodalTangent

open Smoothing Lines Charts.AffineTangentLift

theorem pointLift_ext_general {Y : Scheme} {sY : Y ⟶ ComplexBase}
    {y : PointsOver ComplexBase (𝟙 ComplexBase) Y sY}
    {v w : Infinitesimal.PointLift Y sY y} (h : v.map = w.map) : v = w := by
  cases v
  cases w
  cases h
  rfl

/-- A point derivation of the actual affine parameter line is determined
by its value on the specified global parameter. -/
theorem baseTangent_zero_iff (D : BaseDifferentialProof.baseChart.Tangent) :
    D = 0 ↔ D.val parameterFunction = 0 := by
  constructor
  · rintro rfl
    rfl
  · intro hD
    let e : BaseDifferentialProof.baseChart.Ring ≃ₐ[ℂ] Polynomial ℂ :=
      AlgEquiv.ofBijective BaseDifferentialProof.baseFunctions
        (ConcreteCategory.bijective_of_isIso
          (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))).hom)
    have heX : e.symm Polynomial.X = parameterFunction := by
      apply e.injective
      rw [AlgEquiv.apply_symm_apply]
      exact (Iso.inv_hom_id_apply
        (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℂ))) Polynomial.X).symm
    have hmaps :
        (Infinitesimal.tangentToDual BaseDifferentialProof.baseChart.evaluation D).comp
            e.symm.toAlgHom =
          (Infinitesimal.tangentToDual BaseDifferentialProof.baseChart.evaluation 0).comp
            e.symm.toAlgHom := by
      apply Polynomial.algHom_ext
      change algebraMap ℂ Infinitesimal.Dual
          (BaseDifferentialProof.baseChart.evaluation (e.symm Polynomial.X)) +
            Infinitesimal.epsilon * algebraMap ℂ Infinitesimal.Dual
              (D.val (e.symm Polynomial.X)) =
        algebraMap ℂ Infinitesimal.Dual
          (BaseDifferentialProof.baseChart.evaluation (e.symm Polynomial.X)) +
            Infinitesimal.epsilon * algebraMap ℂ Infinitesimal.Dual (0 : ℂ)
      rw [heX, hD]
    apply (Infinitesimal.tangentToDual_bijective
      BaseDifferentialProof.baseChart.evaluation).injective
    apply Subtype.ext
    apply AlgHom.ext
    intro a
    have ha := congrArg (fun q : Polynomial ℂ →ₐ[ℂ] Infinitesimal.Dual => q (e a)) hmaps
    simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      AlgEquiv.symm_apply_apply] using ha

variable {n : ℕ} {X : ContactFanoManifold n} {D : SuitablePair X}
variable (G : Germ D)

/-- The kernel condition is equivalent to the actual infinitesimal
parameter map being the constant map to zero. -/
theorem vertical_iff_constant_base (v : G.chart.Tangent) :
    G.baseDifferential v = 0 ↔
      (lift G.chart v).map ≫ G.inclusion ≫ G.hom.toBase =
        Infinitesimal.dualToC ≫ scalarPoint 0 := by
  have hb : (BaseDifferentialProof.smoothingChartMap G).differential v = 0 ↔
      G.baseDifferential v = 0 :=
    baseTangent_zero_iff ((BaseDifferentialProof.smoothingChartMap G).differential v)
  rw [← hb, differential_zero_iff]
  rfl

/-- The specified point of the full relative Hom scheme. -/
def homPoint : PointsOver ComplexBase (𝟙 ComplexBase) G.hom.parameter
    (G.hom.toBase ≫ affineLineToC) :=
  ⟨G.chart.point.val ≫ G.inclusion, by
    rw [Category.assoc, G.chart_overC, G.chart.point.property]⟩

/-- A vertical Hom lift retains its entire nonreduced parameter map. -/
abbrev VerticalHomLift :=
  {v : Infinitesimal.PointLift G.hom.parameter
      (G.hom.toBase ≫ affineLineToC) (homPoint G) //
    v.map ≫ G.hom.toBase = Infinitesimal.dualToC ≫ scalarPoint 0}

def homLift (v : LinearMap.ker G.baseDifferential) : VerticalHomLift G :=
  ⟨push G.inclusion G.chart_overC rfl (lift G.chart v.val),
    by simpa only [push, Category.assoc] using
      (vertical_iff_constant_base G v.val).mp v.property⟩

theorem homLift_map (v : LinearMap.ker G.baseDifferential) :
    (homLift G v).val.map = (lift G.chart v.val).map ≫ G.inclusion := rfl

/-- The open chart loses no infinitesimal lift centered at its marked
point, since a nilpotent thickening has the same topological support. -/
theorem homLift_bijective : Function.Bijective (homLift G) := by
  letI : IsOpenImmersion G.inclusion := G.openImmersion
  constructor
  · intro v w h
    apply Subtype.ext
    apply lift_injective G.chart
    apply pointLift_ext G.chart
    apply (cancel_mono G.inclusion).mp
    exact congrArg (fun q : VerticalHomLift G => q.val.map) h
  · intro v
    have hr : Set.range v.val.map ⊆ Set.range G.inclusion := by
      rw [LocalVelocityComparison.pointLift_range v.val]
      rintro _ ⟨z, rfl⟩
      exact ⟨G.chart.point.val z, rfl⟩
    let w : Infinitesimal.PointLift G.chart.scheme G.chart.toC G.chart.point :=
      { map := IsOpenImmersion.lift G.inclusion v.val.map hr
        overC := by
          rw [← G.chart_overC, ← Category.assoc, IsOpenImmersion.lift_fac, v.val.overC]
        reduces := by
          apply (cancel_mono G.inclusion).mp
          rw [Category.assoc, IsOpenImmersion.lift_fac, v.val.reduces]
          rfl }
    obtain ⟨z, hz⟩ := lift_surjective G.chart w
    have hzmap : (lift G.chart z).map ≫ G.inclusion = v.val.map := by
      rw [hz]
      exact IsOpenImmersion.lift_fac _ _ _
    have hzbase : G.baseDifferential z = 0 :=
      (vertical_iff_constant_base G z).mpr (by
        rw [← Category.assoc, hzmap]
        exact v.property)
    refine ⟨⟨z, hzbase⟩, ?_⟩
    apply Subtype.ext
    exact pointLift_ext_general hzmap

/-- The explicit equivalence still has the normalized chart lift as its
forward map; no vector-space identification is chosen here. -/
def homLiftEquiv : LinearMap.ker G.baseDifferential ≃ VerticalHomLift G :=
  Equiv.ofBijective (homLift G) (homLift_bijective G)

abbrev constantDualParameter : Infinitesimal.DualScheme ⟶ AffineLine :=
  Infinitesimal.dualToC ≫ scalarPoint 0

/-- The iterated pullback isomorphism identifies the actual fixed-fibre
dual thickening with the original source pulled back along the constant
dual-number parameter. Both projections are the canonical ones. -/
def sourceThickeningIso (F : StandardSource) :
    DualThickening.space (centralBase F) ≅ SourceOver F constantDualParameter :=
  pullbackLeftPullbackSndIso F.parameter (scalarPoint 0) Infinitesimal.dualToC

@[reassoc] theorem sourceThickeningIso_hom_fst (F : StandardSource) :
    (sourceThickeningIso F).hom ≫ pullback.fst F.parameter constantDualParameter =
      DualThickening.projection (centralBase F) ≫ pullback.fst F.parameter (scalarPoint 0) :=
  pullbackLeftPullbackSndIso_hom_fst _ _ _

@[reassoc] theorem sourceThickeningIso_hom_snd (F : StandardSource) :
    (sourceThickeningIso F).hom ≫ pullback.snd F.parameter constantDualParameter =
      DualThickening.parameter (centralBase F) :=
  pullbackLeftPullbackSndIso_hom_snd _ _ _

theorem sourceThickeningIso_inv_overC (F : StandardSource) :
    (sourceThickeningIso F).inv ≫ DualThickening.toC (centralBase F) =
      pullback.snd F.parameter constantDualParameter ≫ Infinitesimal.dualToC :=
  pullbackLeftPullbackSndIso_inv_fst_snd _ _ _

/-- Restricting the actual relative-Hom evaluation to the reduction of a
constant-base dual point is its evaluation at the actual reduced Hom point. -/
theorem evaluation_reduction_map (a : Infinitesimal.DualScheme ⟶ G.hom.parameter)
    (ha : a ≫ G.hom.toBase = constantDualParameter) :
    DualThickening.zeroSection (centralBase G.source) ≫
        (sourceThickeningIso G.source).hom ≫
          sourceBaseChangeMap G.source constantDualParameter G.hom.toBase a ha =
      sourceBaseChangeMap G.source (scalarPoint 0) G.hom.toBase
        (Infinitesimal.origin ≫ a)
        (by rw [Category.assoc, ha, ← Category.assoc,
          DualThickening.origin_overC, Category.id_comp]) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, sourceBaseChangeMap, pullback.lift_fst,
      sourceThickeningIso_hom_fst]
    simpa only [Category.assoc, Category.id_comp] using
      congrArg
        (fun k : CentralFiber G.source ⟶ CentralFiber G.source =>
          k ≫ pullback.fst G.source.parameter (scalarPoint 0))
        (DualThickening.zeroSection_projection (centralBase G.source))
  · simp only [Category.assoc, sourceBaseChangeMap, pullback.lift_snd,
      sourceThickeningIso_hom_snd_assoc]
    simpa only [centralBase, Category.assoc] using
      congrArg
        (fun k : CentralFiber G.source ⟶ Infinitesimal.DualScheme => k ≫ a)
        (DualThickening.zeroSection_parameter (centralBase G.source))

/-- Pull the actual universal map back along a vertical nonreduced Hom
point. This constructs a deformation of the exact central map. -/
def deformationOfHomLift (v : VerticalHomLift G) :
    FamilyVariation.Deformation (centralBase G.source) X.variety.structureMap (centralMap G) where
  map := (sourceThickeningIso G.source).hom ≫
    sourceBaseChangeMap G.source constantDualParameter G.hom.toBase v.val.map v.property ≫
      G.hom.evaluation
  overC := by
    rw [Category.assoc, Category.assoc, G.hom.overC,
      sourceBaseChangeMap, pullback.lift_snd_assoc]
    simp only [Category.assoc]
    rw [v.val.overC]
    exact (sourceThickeningIso_hom_snd_assoc G.source Infinitesimal.dualToC).trans
      (DualThickening.parameter_overC (centralBase G.source))
  reduces := by
    have h := congrArg
      (fun k : CentralFiber G.source ⟶ SourceOver G.source G.hom.toBase =>
        k ≫ G.hom.evaluation)
      (evaluation_reduction_map G v.val.map v.property)
    simpa only [Category.assoc, v.val.reduces, homPoint, centralMap] using h

/-- Full-test-scheme universality is essential in both directions:
every actual central-map deformation is represented over Spec(Dual). -/
theorem deformationOfHomLift_bijective : Function.Bijective (deformationOfHomLift G) := by
  constructor
  · intro v w h
    have hm := congrArg (fun q : FamilyVariation.Deformation
      (centralBase G.source) X.variety.structureMap (centralMap G) => q.map) h
    have he : sourceBaseChangeMap G.source constantDualParameter G.hom.toBase
          v.val.map v.property ≫ G.hom.evaluation =
        sourceBaseChangeMap G.source constantDualParameter G.hom.toBase
          w.val.map w.property ≫ G.hom.evaluation :=
      (cancel_epi (sourceThickeningIso G.source).hom).mp hm
    have hp : (⟨v.val.map, v.property⟩ :
        {a : Infinitesimal.DualScheme ⟶ G.hom.parameter //
          a ≫ G.hom.toBase = constantDualParameter}) = ⟨w.val.map, w.property⟩ := by
      apply (G.hom.universal Infinitesimal.DualScheme constantDualParameter).injective
      exact Subtype.ext he
    apply Subtype.ext
    exact pointLift_ext_general (congrArg Subtype.val hp)
  · intro E
    let f : SourceOver G.source constantDualParameter ⟶ X.variety.scheme :=
      (sourceThickeningIso G.source).inv ≫ E.map
    have hf : f ≫ X.variety.structureMap =
        pullback.snd G.source.parameter constantDualParameter ≫
          constantDualParameter ≫ affineLineToC := by
      dsimp only [f]
      rw [Category.assoc, E.overC, sourceThickeningIso_inv_overC]
      simp only [constantDualParameter, Category.assoc, scalarPoint_overC, Category.comp_id]
    obtain ⟨a, ha⟩ := (G.hom.universal Infinitesimal.DualScheme constantDualParameter).surjective
      ⟨f, hf⟩
    have hae : sourceBaseChangeMap G.source constantDualParameter G.hom.toBase
        a.val a.property ≫ G.hom.evaluation = f := congrArg Subtype.val ha
    have hab : (Infinitesimal.origin ≫ a.val) ≫ G.hom.toBase = scalarPoint 0 := by
      rw [Category.assoc, a.property, constantDualParameter,
        ← Category.assoc, DualThickening.origin_overC, Category.id_comp]
    have har : sourceBaseChangeMap G.source (scalarPoint 0) G.hom.toBase
        (Infinitesimal.origin ≫ a.val) hab ≫ G.hom.evaluation = centralMap G := by
      rw [← evaluation_reduction_map G a.val a.property]
      rw [Category.assoc, Category.assoc, hae]
      change DualThickening.zeroSection (centralBase G.source) ≫
        (sourceThickeningIso G.source).hom ≫
          (sourceThickeningIso G.source).inv ≫ E.map = centralMap G
      rw [Iso.hom_inv_id_assoc]
      exact E.reduces
    have hac : Infinitesimal.origin ≫ a.val = (homPoint G).val := by
      have hp : (⟨Infinitesimal.origin ≫ a.val, hab⟩ :
          {a : ComplexBase ⟶ G.hom.parameter // a ≫ G.hom.toBase = scalarPoint 0}) =
          ⟨(homPoint G).val, G.centre_base⟩ := by
        apply (G.hom.universal ComplexBase (scalarPoint 0)).injective
        exact Subtype.ext har
      exact congrArg Subtype.val hp
    let v : VerticalHomLift G :=
      ⟨{ map := a.val
         overC := by
           rw [← Category.assoc, a.property, constantDualParameter,
             Category.assoc, scalarPoint_overC, Category.comp_id]
         reduces := hac }, a.property⟩
    refine ⟨v, FamilyVariation.Deformation.ext ?_⟩
    change (sourceThickeningIso G.source).hom ≫
        sourceBaseChangeMap G.source constantDualParameter G.hom.toBase
          a.val a.property ≫ G.hom.evaluation = E.map
    rw [hae]
    change (sourceThickeningIso G.source).hom ≫ (sourceThickeningIso G.source).inv ≫ E.map = E.map
    exact Iso.hom_inv_id_assoc _ _

def deformationEquiv : LinearMap.ker G.baseDifferential ≃
    FamilyVariation.Deformation (centralBase G.source) X.variety.structureMap (centralMap G) :=
  (homLiftEquiv G).trans
    (Equiv.ofBijective (deformationOfHomLift G) (deformationOfHomLift_bijective G))

section GenericVariation

variable {Y Z : Scheme} {d : ℕ} (M : SmoothProperComplexVariety d)
variable {sY : Y ⟶ ComplexBase} {f : Y ⟶ M.scheme}

/-- The normalization used by the existing family variation is faithful
on the original tangent-bundle sections. -/
theorem cotangentNormalization_injective : Function.Injective
    (fun s : CSections sY (pullbackModule f (tangentSheaf M.structureMap)) =>
      TwoChartSections.internalHomSectionAddEquiv _ _
        (sectionFromValue s ≫ dualBaseChange f (cotangentSheaf M.structureMap))) := by
  letI := dualBaseChange_isIso f (smooth_cotangent_rank M.structureMap d M.smooth)
  intro s t h
  have hs := congrArg TwoChartSections.homSection h
  simp only [TwoChartSections.homSection_internalHomSectionAddEquiv] at hs
  have ht : sectionFromValue s = sectionFromValue t :=
    (cancel_mono (dualBaseChange f (cotangentSheaf M.structureMap))).mp hs
  simpa only [sectionFromValue_spec] using congrArg sectionValue ht

/-- The generic published lifting torsor gives bijectivity of the
already constructed, normalized variation. No endpoint map enters here. -/
theorem variation_bijective (hf : f ≫ M.structureMap = sY) :
    Function.Bijective (fun E : FamilyVariation.Deformation sY M.structureMap f =>
      E.variation M) := by
  have hc := StandardInputs.InfinitesimalGeometry.firstOrder_cotangentHom_bijective
    sY M.structureMap f hf
  constructor
  · intro E F h
    apply hc.injective
    change E.cotangentHom = F.cotangentHom
    have hn := congrArg
      (fun s : CSections sY (pullbackModule f (tangentSheaf M.structureMap)) =>
        TwoChartSections.internalHomSectionAddEquiv _ _
          (sectionFromValue s ≫ dualBaseChange f (cotangentSheaf M.structureMap))) h
    exact (E.variation_normalized M).symm.trans (hn.trans (F.variation_normalized M))
  · intro s
    obtain ⟨E, hE⟩ := hc.surjective
      (TwoChartSections.internalHomSectionAddEquiv _ _
        (sectionFromValue s ≫ dualBaseChange f (cotangentSheaf M.structureMap)))
    refine ⟨E, cotangentNormalization_injective M ?_⟩
    exact (E.variation_normalized M).trans hE

open ContactDerivativeIsoProof in
/-- Precomposition of a functional is the actual contravariant dual map
on its Hom section. The equality is proved against all local sections. -/
theorem homSection_dualMap {T : Scheme} {E F : OModule T}
    (a : E ⟶ F) (h : F ⟶ structureModule T) :
    TwoChartSections.homSection h ≫ dualMap a = TwoChartSections.homSection (a ≫ h) := by
  apply (internalHomPresentation E (structureModule T)).hom_ext
  apply ((tensorPresentation (structureModule T) E).universal (structureModule T)).injective
  apply sheafBilinearMap_ext
  intro U r e
  change (internalHomPresentation E (structureModule T)).evaluate.app U
      ((tensorMap (TwoChartSections.homSection h ≫ dualMap a) (𝟙 E)).app U
        ((tensorPresentation (structureModule T) E).pair.apply U r e)) =
    (internalHomPresentation E (structureModule T)).evaluate.app U
      ((tensorMap (TwoChartSections.homSection (a ≫ h)) (𝟙 E)).app U
        ((tensorPresentation (structureModule T) E).pair.apply U r e))
  rw [tensorMap_apply, tensorMap_apply]
  change (dualEvaluation E).apply U
      ((dualMap a).app U
        (Scheme.Modules.Hom.app (TwoChartSections.homSection h) U r)) e =
    (dualEvaluation E).apply U
      (Scheme.Modules.Hom.app (TwoChartSections.homSection (a ≫ h)) U r) e
  rw [ContactDerivativeIsoProof.dualMap_evaluate]
  exact (FamilyVariation.homSection_evaluate h U r (a.app U e)).trans
    (FamilyVariation.homSection_evaluate (a ≫ h) U r e).symm

/-- Source restriction of a first-order family restricts its original
tangent section through the fixed composition-pullback isomorphism. -/
theorem section_pullback (E : FamilyVariation.Deformation sY M.structureMap f)
    {sZ : Z ⟶ ComplexBase} (g : Z ⟶ Y) (hg : g ≫ sY = sZ) :
    pullSection g (E.section M) ≫
        (compositionPullback g f (g ≫ f) rfl (tangentSheaf M.structureMap)).hom =
      (E.pullback g hg).section M := by
  letI := dualBaseChange_isIso (g ≫ f)
    (smooth_cotangent_rank M.structureMap d M.smooth)
  apply (cancel_mono (dualBaseChange (g ≫ f) (cotangentSheaf M.structureMap))).mp
  rw [(E.pullback g hg).section_normalized]
  simp only [compositionPullback, Iso.trans_hom, eqToIso_refl,
    Iso.refl_hom, Iso.app_hom, Category.comp_id]
  rw [Category.assoc, ContactDerivativeIsoProof.dualBaseChange_comp]
  rw [← Category.assoc, ← pullSection_naturality, E.section_normalized]
  rw [← Category.assoc, FamilyVariation.homSection_pullback, homSection_dualMap]
  rw [E.pullback_cotangentHom]

/-- The same naturality on the actual complex vector spaces of sections. -/
theorem variation_pullback (E : FamilyVariation.Deformation sY M.structureMap f)
    {sZ : Z ⟶ ComplexBase} (g : Z ⟶ Y) (hg : g ≫ sY = sZ) :
    onCSections sZ
        (compositionPullback g f (g ≫ f) rfl (tangentSheaf M.structureMap)).hom
        (pullCSections g sZ sY hg (pullbackModule f (tangentSheaf M.structureMap))
          (E.variation M)) = (E.pullback g hg).variation M := by
  change sectionValue (pullSection g (sectionFromValue (sectionValue (E.section M))) ≫
    (compositionPullback g f (g ≫ f) rfl (tangentSheaf M.structureMap)).hom) = _
  rw [sectionFromValue_sectionValue, section_pullback]
  rfl

end GenericVariation

/-- The forward map is the actual epsilon coefficient of the actual
relative universal family, as a section of the original central bundle. -/
def verticalVariation (v : LinearMap.ker G.baseDifferential) : CentralSections G :=
  (deformationEquiv G v).variation X.variety

theorem verticalVariation_bijective : Function.Bijective (verticalVariation G) :=
  (variation_bijective X.variety (centralMap_over G)).comp (deformationEquiv G).bijective

namespace AffineIntrinsic

variable (A : Charts.PointedAffine) {d : ℕ} (M : SmoothProperComplexVariety d)
variable (x : ComplexPoint M) (j : A.scheme ⟶ M.scheme)
variable [IsOpenImmersion j] (hj : j ≫ M.structureMap = A.toC)
variable (hx : A.point.val ≫ j = x.map)

/-- The affine spectrum of the specified pointed chart, with its actual
complex algebra and point. This is a change of presentation only. -/
def targetChart : GlobalVelocity.TargetChart M x where
  Ring := A.Ring
  commRing := inferInstance
  algebra := inferInstance
  inclusion := A.scheme.isoSpec.inv ≫ j
  openImmersion := inferInstance
  overC := by
    rw [Category.assoc, hj, ← GlobalVelocity.toSpecΓ_overC A.toC,
      ← Category.assoc, Scheme.isoSpec_inv_toSpecΓ]
    exact Category.id_comp
      (DirectionCones.affineBaseMap (SectionAlgebra.Functions A.toC ⊤))
  point := A.point.val ≫ A.scheme.isoSpec.hom
  atPoint := by rw [Category.assoc, Iso.hom_inv_id_assoc, hx]

/-- The spectrum presentation has exactly the original chart's point
evaluation, including its fixed complex-algebra structure. -/
theorem targetChart_evaluation :
    (targetChart A M x j hj hx).evaluation = A.evaluation := by
  apply AlgHom.ext
  intro a
  change A.Ring at a
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      ((A.point.val ≫ A.scheme.isoSpec.hom).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of A.Ring)).inv a)) =
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (A.point.val.appTop a)
  rw [Scheme.Hom.comp_appTop]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      (A.point.val.appTop (A.scheme.toSpecΓ.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of A.Ring)).inv a))) = _
  rw [Scheme.toSpecΓ_appTop]
  exact congrArg (fun b : A.Ring =>
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (A.point.val.appTop b))
    (Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of A.Ring)) a)

/-- Equality of the actual evaluations transports derivations without
changing their underlying linear functions. -/
def chartDerivations : A.Tangent ≃ₗ[ℂ]
    Infinitesimal.Tangent (targetChart A M x j hj hx).Ring
      (targetChart A M x j hj hx).evaluation :=
  LinearEquiv.ofEq _ _ (by rw [targetChart_evaluation]; rfl)

theorem chartDerivations_value (v : A.Tangent) :
    (chartDerivations A M x j hj hx v).val = v.val := rfl

/-- The canonical comparison to the original tangent-sheaf fibre. -/
def tangentEquiv : A.Tangent ≃ₗ[ℂ] TangentFiber M x :=
  (chartDerivations A M x j hj hx).trans
    (IntrinsicTangent.chartEquivalence (targetChart A M x j hj hx)).symm

/-- Both constructions use the same Spec map of the normalized dual
algebra homomorphism. Hence they agree as entire infinitesimal maps. -/
theorem lift_eq_chartLift (v : A.Tangent) :
    push j hj hx (lift A v) =
      IntrinsicTangent.chartLift (targetChart A M x j hj hx)
        (chartDerivations A M x j hj hx v) := by
  apply pointLift_ext_general
  change (Spec.map (CommRingCat.ofHom
      (Infinitesimal.tangentToDual A.evaluation v).toRingHom) ≫
        A.scheme.isoSpec.inv) ≫ j =
    Spec.map (CommRingCat.ofHom
      (Infinitesimal.tangentToDual (targetChart A M x j hj hx).evaluation
        (chartDerivations A M x j hj hx v)).toRingHom) ≫
      (A.scheme.isoSpec.inv ≫ j)
  rw [Category.assoc]
  congr 2
  apply CommRingCat.hom_ext
  ext a
  change algebraMap ℂ Infinitesimal.Dual (A.evaluation a) +
      Infinitesimal.epsilon * algebraMap ℂ Infinitesimal.Dual (v.val a) =
    algebraMap ℂ Infinitesimal.Dual ((targetChart A M x j hj hx).evaluation a) +
      Infinitesimal.epsilon * algebraMap ℂ Infinitesimal.Dual (v.val a)
  rw [targetChart_evaluation]
  rfl

theorem tangentEquiv_pointVector (v : A.Tangent) :
    tangentEquiv A M x j hj hx v =
      SourceTangent.pointVector M x (push j hj hx (lift A v)) := by
  rw [lift_eq_chartLift]
  exact IntrinsicTangent.chartEquivalence_symm_apply _ _

end AffineIntrinsic

/-- An open immersion of actual pointed affine charts induces an
isomorphism on point derivations. Surjectivity factors the entire dual
point through the open, rather than only its underlying topological point. -/
theorem open_differential_bijective {A B : Charts.PointedAffine}
    (f : Charts.Hom A B) [IsOpenImmersion f.map] :
    Function.Bijective f.differential := by
  constructor
  · intro v w h
    apply lift_injective A
    apply pointLift_ext A
    apply (cancel_mono f.map).mp
    rw [lift_natural f v, lift_natural f w, h]
  · intro w
    have hr : Set.range (lift B w).map ⊆ Set.range f.map := by
      rw [LocalVelocityComparison.pointLift_range]
      rintro _ ⟨z, rfl⟩
      refine ⟨A.point.val z, ?_⟩
      exact congrArg (fun k : ComplexBase ⟶ B.scheme => k z) f.atCentre
    let v : Infinitesimal.PointLift A.scheme A.toC A.point :=
      { map := IsOpenImmersion.lift f.map (lift B w).map hr
        overC := by
          rw [← f.overC, ← Category.assoc, IsOpenImmersion.lift_fac,
            (lift B w).overC]
        reduces := by
          apply (cancel_mono f.map).mp
          rw [Category.assoc, IsOpenImmersion.lift_fac,
            (lift B w).reduces, f.atCentre] }
    obtain ⟨v₀, hv₀⟩ := lift_surjective A v
    refine ⟨v₀, lift_injective B ?_⟩
    apply pointLift_ext B
    rw [← lift_natural f v₀, hv₀]
    exact IsOpenImmersion.lift_fac _ _ _

def openDifferentialEquiv {A B : Charts.PointedAffine}
    (f : Charts.Hom A B) [IsOpenImmersion f.map] : A.Tangent ≃ₗ[ℂ] B.Tangent :=
  LinearEquiv.ofBijective f.differential (open_differential_bijective f)

/-- For any actual morphism from a pointed affine scheme, the original
tangent vector of its pushed dual point depends linearly on the chart
derivation. Shrinking into an actual affine target neighborhood proves
this without a smoothness hypothesis on the source. -/
theorem pointVector_push_linear {A : Charts.PointedAffine} {d : ℕ}
    (M : SmoothProperComplexVariety d) (x : ComplexPoint M)
    (g : A.scheme ⟶ M.scheme) (hg : g ≫ M.structureMap = A.toC)
    (hx : A.point.val ≫ g = x.map) :
    ∃ e : A.Tangent →ₗ[ℂ] TangentFiber M x,
      ∀ v, e v = SourceTangent.pointVector M x (push g hg hx (lift A v)) := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := M.scheme) (x := x.map (default : PrimeSpectrum ℂ))
    (U := ⊤) (show x.map (default : PrimeSpectrum ℂ) ∈ (⊤ : M.scheme.Opens) by trivial)
  have hxUr := GermProof.point_range_in_open x.map U hxU
  let B := GermProof.chartOfOpen M.structureMap
    ⟨x.map, x.overC⟩ U hU hxUr
  have hp : A.point.val (default : PrimeSpectrum ℂ) ∈ g ⁻¹ᵁ U := by
    change (A.point.val ≫ g) (default : PrimeSpectrum ℂ) ∈ U
    rw [hx]
    exact hxU
  obtain ⟨V, hV, hpV, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (X := A.scheme) (x := A.point.val (default : PrimeSpectrum ℂ))
    (U := g ⁻¹ᵁ U) hp
  have hpVr := GermProof.point_range_in_open A.point.val V hpV
  let A' := GermProof.chartOfOpen A.toC A.point V hV hpVr
  let i : Charts.Hom A' A :=
    { map := V.ι
      overC := rfl
      atCentre := GermProof.chartOfOpen_point A.toC A.point V hV hpVr }
  letI : IsOpenImmersion i.map := inferInstanceAs (IsOpenImmersion V.ι)
  have hmap : Set.range (V.ι ≫ g) ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    exact hVU z.property
  let f : Charts.Hom A' B :=
    { map := IsOpenImmersion.lift U.ι (V.ι ≫ g) hmap
      overC := by
        change IsOpenImmersion.lift U.ι (V.ι ≫ g) hmap ≫
          (U.ι ≫ M.structureMap) = V.ι ≫ A.toC
        rw [← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, hg]
      atCentre := by
        apply (cancel_mono U.ι).mp
        rw [Category.assoc, IsOpenImmersion.lift_fac,
          ← Category.assoc, i.atCentre, hx]
        exact (GermProof.chartOfOpen_point M.structureMap
          ⟨x.map, x.overC⟩ U hU hxUr).symm }
  let eB := AffineIntrinsic.tangentEquiv B M x U.ι rfl
    (GermProof.chartOfOpen_point M.structureMap ⟨x.map, x.overC⟩ U hU hxUr)
  let eI := openDifferentialEquiv i
  refine ⟨eB.toLinearMap.comp (f.differential.comp eI.symm.toLinearMap), ?_⟩
  intro v
  change eB (f.differential (eI.symm v)) = _
  rw [AffineIntrinsic.tangentEquiv_pointVector]
  congr 1
  apply pointLift_ext_general
  change (lift B (f.differential (eI.symm v))).map ≫ U.ι =
    (lift A v).map ≫ g
  rw [← lift_natural, Category.assoc, IsOpenImmersion.lift_fac,
    ← Category.assoc]
  change ((lift A' (eI.symm v)).map ≫ i.map) ≫ g = _
  rw [lift_natural]
  change (lift A (eI (eI.symm v))).map ≫ g = _
  rw [LinearEquiv.apply_symm_apply]

/-- The actual zero fibre of the specified affine Hom chart. It is
affine as a pullback of affine schemes, even if it is singular. -/
def zeroChart : Charts.PointedAffine where
  scheme := pullback (G.inclusion ≫ G.hom.toBase) (scalarPoint 0)
  affine := inferInstance
  toC := pullback.snd (G.inclusion ≫ G.hom.toBase) (scalarPoint 0)
  point := ⟨pullback.lift G.chart.point.val (𝟙 ComplexBase)
    (by simpa only [Category.id_comp] using G.centre_base), by simp⟩

def zeroChartMap : Charts.Hom (zeroChart G) G.chart where
  map := pullback.fst (G.inclusion ≫ G.hom.toBase) (scalarPoint 0)
  overC := by
    calc
      pullback.fst (G.inclusion ≫ G.hom.toBase) (scalarPoint 0) ≫ G.chart.toC =
          (pullback.fst (G.inclusion ≫ G.hom.toBase) (scalarPoint 0) ≫
            (G.inclusion ≫ G.hom.toBase)) ≫ affineLineToC := by
        simp only [Category.assoc, G.chart_overC]
      _ = (pullback.snd (G.inclusion ≫ G.hom.toBase) (scalarPoint 0) ≫
          scalarPoint 0) ≫ affineLineToC :=
        congrArg (fun k => k ≫ affineLineToC)
          (pullback.condition (f := G.inclusion ≫ G.hom.toBase) (g := scalarPoint 0))
      _ = (zeroChart G).toC := by
        rw [Category.assoc, scalarPoint_overC, Category.comp_id]
        rfl
  atCentre := pullback.lift_fst _ _ _

/-- The tangent of the zero-fibre inclusion has image in the specified
kernel, by equality of the entire infinitesimal parameter map. -/
def zeroDirection : (zeroChart G).Tangent →ₗ[ℂ] LinearMap.ker G.baseDifferential where
  toFun v := ⟨(zeroChartMap G).differential v, by
    apply (vertical_iff_constant_base G _).mpr
    rw [← lift_natural (zeroChartMap G) v, Category.assoc]
    change (lift (zeroChart G) v).map ≫
        pullback.fst (G.inclusion ≫ G.hom.toBase) (scalarPoint 0) ≫
          (G.inclusion ≫ G.hom.toBase) = _
    rw [pullback.condition, ← Category.assoc]
    exact congrArg (fun k => k ≫ scalarPoint 0) (lift (zeroChart G) v).overC⟩
  map_add' := by intro v w; apply Subtype.ext; exact map_add _ v w
  map_smul' := by intro c v; apply Subtype.ext; exact map_smul _ c v

/-- The universal property of the actual fibre square proves the
vertical tangent identification. No smoothness or tangent dimension
calculation is needed. -/
theorem zeroDirection_bijective : Function.Bijective (zeroDirection G) := by
  constructor
  · intro v w h
    have hvw := congrArg (fun z : LinearMap.ker G.baseDifferential => z.val) h
    change (zeroChartMap G).differential v = (zeroChartMap G).differential w at hvw
    apply lift_injective (zeroChart G)
    apply pointLift_ext (zeroChart G)
    apply pullback.hom_ext
    · change (lift (zeroChart G) v).map ≫ (zeroChartMap G).map =
        (lift (zeroChart G) w).map ≫ (zeroChartMap G).map
      exact (lift_natural (zeroChartMap G) v).trans
        ((congrArg (fun z : G.chart.Tangent => (lift G.chart z).map) hvw).trans
          (lift_natural (zeroChartMap G) w).symm)
    · exact (lift (zeroChart G) v).overC.trans (lift (zeroChart G) w).overC.symm
  · intro v
    let w : Infinitesimal.PointLift (zeroChart G).scheme (zeroChart G).toC
        (zeroChart G).point :=
      { map := pullback.lift (lift G.chart v.val).map Infinitesimal.dualToC
          ((vertical_iff_constant_base G v.val).mp v.property)
        overC := pullback.lift_snd _ _ _
        reduces := by
          apply pullback.hom_ext
          · simp only [Category.assoc, pullback.lift_fst, zeroChart,
              (lift G.chart v.val).reduces]
          · simp only [Category.assoc, pullback.lift_snd, zeroChart,
              DualThickening.origin_overC] }
    obtain ⟨z, hz⟩ := lift_surjective (zeroChart G) w
    refine ⟨z, ?_⟩
    apply Subtype.ext
    apply lift_injective G.chart
    apply pointLift_ext G.chart
    change (lift G.chart ((zeroChartMap G).differential z)).map = _
    rw [← lift_natural, hz]
    exact pullback.lift_fst _ _ _

def zeroDirectionEquiv : (zeroChart G).Tangent ≃ₗ[ℂ] LinearMap.ker G.baseDifferential :=
  LinearEquiv.ofBijective (zeroDirection G) (zeroDirection_bijective G)

/-- An arbitrary actual point of the nodal source is held fixed over
the zero fibre of the Hom chart. This supplies an actual evaluation
morphism, including at the node. -/
def zeroEvaluationSource
    (q : PointsOver ComplexBase (𝟙 ComplexBase) (CentralFiber G.source)
      (centralBase G.source)) :
    (zeroChart G).scheme ⟶ SourceOver G.source G.hom.toBase :=
  pullback.lift
    ((zeroChart G).toC ≫ q.val ≫ pullback.fst G.source.parameter (scalarPoint 0))
    ((zeroChartMap G).map ≫ G.inclusion)
    (by
      have hq : q.val ≫ pullback.snd G.source.parameter (scalarPoint 0) =
          𝟙 ComplexBase := q.property
      rw [Category.assoc, Category.assoc, pullback.condition,
        ← Category.assoc q.val, hq, Category.id_comp]
      simpa only [zeroChart, zeroChartMap, Category.assoc] using
        (pullback.condition (f := G.inclusion ≫ G.hom.toBase)
          (g := scalarPoint 0)).symm)

def zeroEvaluation
    (q : PointsOver ComplexBase (𝟙 ComplexBase) (CentralFiber G.source)
      (centralBase G.source)) : (zeroChart G).scheme ⟶ X.variety.scheme :=
  zeroEvaluationSource G q ≫ G.hom.evaluation

theorem zeroEvaluation_over
    (q : PointsOver ComplexBase (𝟙 ComplexBase) (CentralFiber G.source)
      (centralBase G.source)) :
    zeroEvaluation G q ≫ X.variety.structureMap = (zeroChart G).toC := by
  rw [zeroEvaluation, Category.assoc, G.hom.overC,
    zeroEvaluationSource, pullback.lift_snd_assoc,
    Category.assoc, G.chart_overC]
  exact (zeroChartMap G).overC

theorem zeroEvaluation_centre
    (q : PointsOver ComplexBase (𝟙 ComplexBase) (CentralFiber G.source)
      (centralBase G.source)) :
    (zeroChart G).point.val ≫ zeroEvaluation G q = q.val ≫ centralMap G := by
  have h : (zeroChart G).point.val ≫ zeroEvaluationSource G q =
      q.val ≫ sourceBaseChangeMap G.source (scalarPoint 0) G.hom.toBase
        (G.chart.point.val ≫ G.inclusion) G.centre_base := by
    apply pullback.hom_ext
    · simp only [Category.assoc, zeroEvaluationSource, sourceBaseChangeMap,
        pullback.lift_fst, pullback.lift_fst_assoc]
      rw [← Category.assoc, (zeroChart G).point.property, Category.id_comp]
    · simp only [Category.assoc, zeroEvaluationSource, sourceBaseChangeMap,
        pullback.lift_snd, pullback.lift_snd_assoc]
      rw [← Category.assoc, (zeroChartMap G).atCentre]
      simpa only [centralBase, Category.assoc, Category.id_comp] using
        (congrArg (fun k => k ≫ G.chart.point.val ≫ G.inclusion) q.property).symm
  simpa only [zeroEvaluation, centralMap, Category.assoc] using
    congrArg (fun k => k ≫ G.hom.evaluation) h

def centralImage
    (q : PointsOver ComplexBase (𝟙 ComplexBase) (CentralFiber G.source)
      (centralBase G.source)) : ComplexPoint X.variety where
  map := q.val ≫ centralMap G
  overC := by rw [Category.assoc, centralMap_over, q.property]

/-- Infer the actual target point from its morphism, retaining the original push. -/
private def pushToMap {S T : Scheme} {sS : S ⟶ ComplexBase} {sT : T ⟶ ComplexBase}
    {s : PointsOver ComplexBase (𝟙 ComplexBase) S sS} {t : ComplexBase ⟶ T}
    (g : S ⟶ T) (hg : g ≫ sT = sS) (hat : s.val ≫ g = t)
    (v : Infinitesimal.PointLift S sS s) :
    Infinitesimal.PointLift T sT
      ⟨t, by rw [← hat, Category.assoc, hg, s.property]⟩ :=
  Charts.AffineTangentLift.push (s := s)
    (t := ⟨t, by rw [← hat, Category.assoc, hg, s.property]⟩) g hg hat v

private theorem pushToMap_eq_push {S T : Scheme}
    {sS : S ⟶ ComplexBase} {sT : T ⟶ ComplexBase}
    {s : PointsOver ComplexBase (𝟙 ComplexBase) S sS}
    {t : PointsOver ComplexBase (𝟙 ComplexBase) T sT}
    (g : S ⟶ T) (hg : g ≫ sT = sS) (hat : s.val ≫ g = t.val)
    (v : Infinitesimal.PointLift S sS s) :
    pushToMap (s := s) (t := t.val) g hg hat v =
      Charts.AffineTangentLift.push (s := s) (t := t) g hg hat v := by
  rfl

section ZeroEvaluationDeformationTarget

local notation "push" => pushToMap

/-- Restriction of the actual universal-family deformation to any
central point is the actual pushed dual point of its zero-fibre
evaluation. This is equality of maps, not merely equality of tangent
dimensions or of underlying topological points. -/
theorem zeroEvaluation_deformation
    (q : PointsOver ComplexBase (𝟙 ComplexBase) (CentralFiber G.source)
      (centralBase G.source)) (v : (zeroChart G).Tangent) :
    (deformationEquiv G (zeroDirection G v)).pullback q.val q.property =
      SourceTangent.pointDeformation
        (push (zeroEvaluation G q) (zeroEvaluation_over G q)
          (zeroEvaluation_centre G q) (lift (zeroChart G) v)) := by
  let w := homLift G (zeroDirection G v)
  have h : DualThickening.map q.val q.property ≫
        (sourceThickeningIso G.source).hom ≫
          sourceBaseChangeMap G.source constantDualParameter G.hom.toBase
            w.val.map w.property =
      DualThickening.parameter (𝟙 ComplexBase) ≫
        (lift (zeroChart G) v).map ≫ zeroEvaluationSource G q := by
    apply pullback.hom_ext
    · simp only [Category.assoc, sourceBaseChangeMap, zeroEvaluationSource,
        pullback.lift_fst, pullback.lift_fst_assoc,
        sourceThickeningIso_hom_fst]
      calc
        _ = DualThickening.projection (𝟙 ComplexBase) ≫ q.val ≫
            pullback.fst G.source.parameter (scalarPoint 0) := by
          rw [← Category.assoc, DualThickening.map_projection, Category.assoc]
        _ = DualThickening.parameter (𝟙 ComplexBase) ≫
            Infinitesimal.dualToC ≫ q.val ≫
              pullback.fst G.source.parameter (scalarPoint 0) := by
          simpa only [DualThickening.toC, Category.comp_id, Category.assoc] using
            (congrArg (fun k => k ≫ q.val ≫
              pullback.fst G.source.parameter (scalarPoint 0))
              (DualThickening.parameter_overC (𝟙 ComplexBase))).symm
        _ = _ := by
          rw [← Category.assoc (lift (zeroChart G) v).map,
            (lift (zeroChart G) v).overC]
    · simp only [Category.assoc, sourceBaseChangeMap, zeroEvaluationSource,
        pullback.lift_snd, pullback.lift_snd_assoc,
        sourceThickeningIso_hom_snd_assoc]
      rw [← Category.assoc, DualThickening.map_parameter]
      change DualThickening.parameter (𝟙 ComplexBase) ≫
          (lift G.chart ((zeroChartMap G).differential v)).map ≫ G.inclusion = _
      rw [← lift_natural, Category.assoc]
  apply FamilyVariation.Deformation.ext
  change DualThickening.map q.val q.property ≫
        (sourceThickeningIso G.source).hom ≫
          sourceBaseChangeMap G.source constantDualParameter G.hom.toBase
            w.val.map w.property ≫ G.hom.evaluation =
      DualThickening.parameter (𝟙 ComplexBase) ≫
        (lift (zeroChart G) v).map ≫ zeroEvaluationSource G q ≫ G.hom.evaluation
  simpa only [Category.assoc] using congrArg (fun k => k ≫ G.hom.evaluation) h

end ZeroEvaluationDeformationTarget

/-- At every actual source point, the central section's value is the
original tangent vector of the same actual evaluation deformation. -/
theorem verticalVariation_value
    (q : PointsOver ComplexBase (𝟙 ComplexBase) (CentralFiber G.source)
      (centralBase G.source)) (v : (zeroChart G).Tangent) :
    fiberComposition (centralMap G) q.val (centralImage G q).map rfl
        (tangentSheaf X.variety.structureMap)
        (evaluateSection (centralBase G.source) (centralBundle G).sheaf
          q.val q.property (verticalVariation G (zeroDirection G v))) =
      SourceTangent.pointVector X.variety (centralImage G q)
        (push (zeroEvaluation G q) (zeroEvaluation_over G q)
          (zeroEvaluation_centre G q) (lift (zeroChart G) v)) := by
  change onCSections (𝟙 ComplexBase)
      (compositionPullback q.val (centralMap G) (q.val ≫ centralMap G) rfl
        (tangentSheaf X.variety.structureMap)).hom
      (pullCSections q.val (𝟙 ComplexBase) (centralBase G.source) q.property
        (pullbackModule (centralMap G) (tangentSheaf X.variety.structureMap))
        ((deformationEquiv G (zeroDirection G v)).variation X.variety)) = _
  rw [variation_pullback, zeroEvaluation_deformation]
  rfl

/-- Point evaluation of the constructed vertical section is linear.
The proof uses the actual evaluation morphism on the affine zero fibre
and the canonical pullback comparison to the original target fibre. -/
theorem verticalVariation_atPoint_linear
    (q : PointsOver ComplexBase (𝟙 ComplexBase) (CentralFiber G.source)
      (centralBase G.source)) :
    ∃ e : LinearMap.ker G.baseDifferential →ₗ[ℂ]
        Fiber (centralBundle G).sheaf q.val,
      ∀ v, e v = evaluateSection (centralBase G.source) (centralBundle G).sheaf
        q.val q.property (verticalVariation G v) := by
  obtain ⟨d, hd⟩ := pointVector_push_linear X.variety (centralImage G q)
    (zeroEvaluation G q) (zeroEvaluation_over G q) (zeroEvaluation_centre G q)
  let c := LinearEquiv.ofBijective
    (fiberComposition (centralMap G) q.val (centralImage G q).map rfl
      (tangentSheaf X.variety.structureMap))
    (fiberComposition_bijective (centralMap G) q.val (centralImage G q).map rfl
      (tangentSheaf X.variety.structureMap))
  let z := zeroDirectionEquiv G
  refine ⟨c.symm.toLinearMap.comp (d.comp z.symm.toLinearMap), ?_⟩
  intro v
  apply c.injective
  change c (c.symm (d (z.symm v))) = _
  rw [LinearEquiv.apply_symm_apply, hd]
  have hv := verticalVariation_value G q (z.symm v)
  have hz : zeroDirection G (z.symm v) = v := z.apply_symm_apply v
  rw [hz] at hv
  exact hv.symm

/-- Complex-point equality detects branch sections because the actual
projective line is reduced and locally of finite type over C. The
normalization injectivity then detects central sections. No reducedness
assumption is added to the nodal fibre. -/
theorem centralSections_ext_points (s t : CentralSections G)
    (h : ∀ q : PointsOver ComplexBase (𝟙 ComplexBase) (CentralFiber G.source)
        (centralBase G.source),
      evaluateSection (centralBase G.source) (centralBundle G).sheaf
          q.val q.property s =
        evaluateSection (centralBase G.source) (centralBundle G).sheaf
          q.val q.property t) : s = t := by
  letI : Smooth P.structureMap := smoothProperComplexVariety_smooth (projectiveLineVariety P)
  letI : AlgebraicGeometry.IsReduced ProjectiveLine :=
    LeBrunSalamon.SchemeStandardInputs.smooth_complex_reduced P.structureMap
  have hpull (q : PointsOver ComplexBase (𝟙 ComplexBase) (CentralFiber G.source)
      (centralBase G.source)) :
      pullSection q.val (sectionFromValue s) = pullSection q.val (sectionFromValue t) := by
    apply (sectionValue_bijective _).injective
    exact h q
  have branch (b : ProjectiveLine ⟶ CentralFiber G.source)
      (hb : b ≫ centralBase G.source = P.structureMap)
      (f : ProjectiveLine ⟶ X.variety.scheme) (hf : b ≫ centralMap G = f) :
      pullSection b (sectionFromValue s) ≫
          (compositionPullback b (centralMap G) f hf
            (tangentSheaf X.variety.structureMap)).hom =
        pullSection b (sectionFromValue t) ≫
          (compositionPullback b (centralMap G) f hf
            (tangentSheaf X.variety.structureMap)).hom := by
    apply LeBrunSalamon.Refinement.ComplexPointSectionDetection.section_eq
      P.structureMap (LeBrunSalamon.PhaseThirtyFive.pullbackBundle f
        (intrinsicTangentBundle X.variety))
    intro p
    let q : PointsOver ComplexBase (𝟙 ComplexBase) (CentralFiber G.source)
        (centralBase G.source) :=
      ⟨p.val ≫ b, by rw [Category.assoc, hb, p.property]⟩
    have hq : q.val ≫ centralMap G = p.val ≫ f := by
      rw [Category.assoc, hf]
    apply (cancel_mono (compositionPullback p.val f (p.val ≫ f) rfl
      (tangentSheaf X.variety.structureMap)).hom).mp
    have hs := CentralSectionMatchingProof.section_branch p.val b (centralMap G)
      f hf q.val rfl (p.val ≫ f) rfl hq
      (E := tangentSheaf X.variety.structureMap) (sectionFromValue s)
    have ht := CentralSectionMatchingProof.section_branch p.val b (centralMap G)
      f hf q.val rfl (p.val ≫ f) rfl hq
      (E := tangentSheaf X.variety.structureMap) (sectionFromValue t)
    exact hs.trans
      ((congrArg
        (fun a : AlgebraicSection (pullbackModule q.val (centralBundle G).sheaf) =>
          a ≫ (compositionPullback q.val (centralMap G) (p.val ≫ f) hq
            (tangentSheaf X.variety.structureMap)).hom) (hpull q)).trans ht.symm)
  apply (normalizationRestriction_bijective G).injective
  apply Subtype.ext
  apply Prod.ext
  · have hl := branch (leftBranch G.marks) (leftBranch_over G.marks)
      D.first.curve.map (centralMap_left G)
    rw [RestrictionProof.left_section, RestrictionProof.left_section] at hl
    change (restrictLeft G s : GlobalSections
        (pullbackModule D.first.curve.map (tangentSheaf X.variety.structureMap))) =
      restrictLeft G t
    exact (sectionFromValue_spec
      (E := pullbackModule D.first.curve.map (tangentSheaf X.variety.structureMap))
      (restrictLeft G s)).symm.trans
        ((congrArg (sectionValue
          (E := pullbackModule D.first.curve.map (tangentSheaf X.variety.structureMap))) hl).trans
          (sectionFromValue_spec
            (E := pullbackModule D.first.curve.map (tangentSheaf X.variety.structureMap))
            (restrictLeft G t)))
  · have hr := branch (rightBranch G.marks) (rightBranch_over G.marks)
      D.second.curve.map (centralMap_right G)
    rw [RestrictionProof.right_section, RestrictionProof.right_section] at hr
    change (restrictRight G s : GlobalSections
        (pullbackModule D.second.curve.map (tangentSheaf X.variety.structureMap))) =
      restrictRight G t
    exact (sectionFromValue_spec
      (E := pullbackModule D.second.curve.map (tangentSheaf X.variety.structureMap))
      (restrictRight G s)).symm.trans
        ((congrArg (sectionValue
          (E := pullbackModule D.second.curve.map (tangentSheaf X.variety.structureMap))) hr).trans
          (sectionFromValue_spec
            (E := pullbackModule D.second.curve.map (tangentSheaf X.variety.structureMap))
            (restrictRight G t)))

theorem verticalVariation_add (v w : LinearMap.ker G.baseDifferential) :
    verticalVariation G (v + w) = verticalVariation G v + verticalVariation G w := by
  apply centralSections_ext_points G
  intro q
  obtain ⟨e, he⟩ := verticalVariation_atPoint_linear G q
  rw [map_add, ← he, ← he, ← he, map_add]

theorem verticalVariation_smul (c : ℂ) (v : LinearMap.ker G.baseDifferential) :
    verticalVariation G (c • v) = c • verticalVariation G v := by
  apply centralSections_ext_points G
  intro q
  obtain ⟨e, he⟩ := verticalVariation_atPoint_linear G q
  rw [map_smul, ← he, ← he, map_smul]

/-- The original kernel is identified with original central tangent
sections by the normalized universal-family variation, now proved linear. -/
def verticalSectionsLinear : LinearMap.ker G.baseDifferential →ₗ[ℂ] CentralSections G where
  toFun := verticalVariation G
  map_add' := verticalVariation_add G
  map_smul' := verticalVariation_smul G

def verticalSectionsEquiv : LinearMap.ker G.baseDifferential ≃ₗ[ℂ] CentralSections G :=
  LinearEquiv.ofBijective (verticalSectionsLinear G) (verticalVariation_bijective G)

def branchRestriction (b : ProjectiveLine ⟶ CentralFiber G.source)
    (hb : b ≫ centralBase G.source = P.structureMap)
    (f : ProjectiveLine ⟶ X.variety.scheme) (hf : b ≫ centralMap G = f) :
    CentralSections G →ₗ[ℂ]
      CSections P.structureMap (pullbackModule f (tangentSheaf X.variety.structureMap)) :=
  (onCSections P.structureMap
    (compositionPullback b (centralMap G) f hf
      (tangentSheaf X.variety.structureMap)).hom).comp
    (pullCSections b P.structureMap (centralBase G.source) hb (centralBundle G).sheaf)

theorem branchRestriction_section (b : ProjectiveLine ⟶ CentralFiber G.source)
    (hb : b ≫ centralBase G.source = P.structureMap)
    (f : ProjectiveLine ⟶ X.variety.scheme) (hf : b ≫ centralMap G = f)
    (s : CentralSections G) :
    sectionFromValue (branchRestriction G b hb f hf s) =
      pullSection b (sectionFromValue s) ≫
        (compositionPullback b (centralMap G) f hf
          (tangentSheaf X.variety.structureMap)).hom := by
  apply (sectionValue_bijective _).injective
  rw [sectionFromValue_spec, sectionValue_comp]
  rfl

def outerBranchPoint (b : ProjectiveLine ⟶ CentralFiber G.source)
    (hb : b ≫ centralBase G.source = P.structureMap) :
    PointsOver ComplexBase (𝟙 ComplexBase) (CentralFiber G.source) (centralBase G.source) :=
  ⟨infinity.map ≫ b, by rw [Category.assoc, hb, infinity.overC]⟩

theorem outerBranchImage (b : ProjectiveLine ⟶ CentralFiber G.source)
    (hb : b ≫ centralBase G.source = P.structureMap)
    (f : ProjectiveLine ⟶ X.variety.scheme) (hf : b ≫ centralMap G = f) :
    infinity.map ≫ f = (centralImage G (outerBranchPoint G b hb)).map := by
  change infinity.map ≫ f = (infinity.map ≫ b) ≫ centralMap G
  rw [Category.assoc, hf]

/-- Pullback coherence identifies evaluation after branch restriction
with evaluation at the same actual point of the central fibre. -/
theorem branchRestriction_value (b : ProjectiveLine ⟶ CentralFiber G.source)
    (hb : b ≫ centralBase G.source = P.structureMap)
    (f : ProjectiveLine ⟶ X.variety.scheme) (hf : b ≫ centralMap G = f)
    (s : CentralSections G) :
    fiberComposition f infinity.map (centralImage G (outerBranchPoint G b hb)).map
        (outerBranchImage G b hb f hf) (tangentSheaf X.variety.structureMap)
        (evaluateSection P.structureMap (pullbackModule f (tangentSheaf X.variety.structureMap))
          infinity.map infinity.overC (branchRestriction G b hb f hf s)) =
      fiberComposition (centralMap G) (outerBranchPoint G b hb).val
        (centralImage G (outerBranchPoint G b hb)).map rfl
        (tangentSheaf X.variety.structureMap)
        (evaluateSection (centralBase G.source) (centralBundle G).sheaf
          (outerBranchPoint G b hb).val (outerBranchPoint G b hb).property s) := by
  have h := CentralSectionMatchingProof.section_branch infinity.map b (centralMap G)
    f hf (outerBranchPoint G b hb).val rfl
    (centralImage G (outerBranchPoint G b hb)).map
    (outerBranchImage G b hb f hf) rfl
    (E := tangentSheaf X.variety.structureMap) (sectionFromValue s)
  have hb' := congrArg
    (fun a : AlgebraicSection (pullbackModule f (tangentSheaf X.variety.structureMap)) =>
      pullSection infinity.map a ≫
        (compositionPullback infinity.map f
          (centralImage G (outerBranchPoint G b hb)).map
          (outerBranchImage G b hb f hf) (tangentSheaf X.variety.structureMap)).hom)
    (branchRestriction_section G b hb f hf s)
  have hv := congrArg
    (sectionValue (E := pullbackModule (centralImage G (outerBranchPoint G b hb)).map
      (tangentSheaf X.variety.structureMap))) (hb'.trans h)
  change sectionValue
      (pullSection infinity.map
          (sectionFromValue (E := pullbackModule f (tangentSheaf X.variety.structureMap))
            (branchRestriction G b hb f hf s)) ≫
        (compositionPullback infinity.map f
          (centralImage G (outerBranchPoint G b hb)).map
          (outerBranchImage G b hb f hf) (tangentSheaf X.variety.structureMap)).hom) =
    sectionValue
      (pullSection (outerBranchPoint G b hb).val
          (sectionFromValue (E := pullbackModule (centralMap G)
            (tangentSheaf X.variety.structureMap)) s) ≫
        (compositionPullback (outerBranchPoint G b hb).val (centralMap G)
          (centralImage G (outerBranchPoint G b hb)).map rfl
          (tangentSheaf X.variety.structureMap)).hom)
  exact hv

/-- The actual endpoint chart is compared with the actual fibre of the
curve pullback, through the original tangent fibre at that endpoint. -/
def endpointFibre (b : ProjectiveLine ⟶ CentralFiber G.source)
    (hb : b ≫ centralBase G.source = P.structureMap)
    (f : ProjectiveLine ⟶ X.variety.scheme) (hf : b ≫ centralMap G = f)
    (A : Charts.PointedAffine) (j : A.scheme ⟶ X.variety.scheme)
    [IsOpenImmersion j] (hj : j ≫ X.variety.structureMap = A.toC)
    (hx : A.point.val ≫ j = infinity.map ≫ f) :
    A.Tangent ≃ₗ[ℂ] Fiber (pullbackModule f (tangentSheaf X.variety.structureMap))
      infinity.map :=
  (AffineIntrinsic.tangentEquiv A X.variety (centralImage G (outerBranchPoint G b hb))
    j hj (hx.trans (outerBranchImage G b hb f hf))).trans
    (LinearEquiv.ofBijective
      (fiberComposition f infinity.map (centralImage G (outerBranchPoint G b hb)).map
        (outerBranchImage G b hb f hf) (tangentSheaf X.variety.structureMap))
      (fiberComposition_bijective f infinity.map (centralImage G (outerBranchPoint G b hb)).map
        (outerBranchImage G b hb f hf) (tangentSheaf X.variety.structureMap))).symm

/-- For a specified endpoint evaluation, both sides are the original
tangent vector of the very same dual-number point of X. -/
theorem zeroEvaluation_chart_value
    (q : PointsOver ComplexBase (𝟙 ComplexBase) (CentralFiber G.source)
      (centralBase G.source))
    (A : Charts.PointedAffine) (j : A.scheme ⟶ X.variety.scheme)
    [IsOpenImmersion j] (hj : j ≫ X.variety.structureMap = A.toC)
    (hx : A.point.val ≫ j = (centralImage G q).map)
    (e : Charts.Hom G.chart A)
    (he : zeroEvaluation G q = (zeroChartMap G).map ≫ e.map ≫ j)
    (v : LinearMap.ker G.baseDifferential) :
    AffineIntrinsic.tangentEquiv A X.variety (centralImage G q) j hj hx
        (e.differential v.val) =
      fiberComposition (centralMap G) q.val (centralImage G q).map rfl
        (tangentSheaf X.variety.structureMap)
        (evaluateSection (centralBase G.source) (centralBundle G).sheaf
          q.val q.property (verticalVariation G v)) := by
  let z := (zeroDirectionEquiv G).symm v
  have hz : zeroDirection G z = v := (zeroDirectionEquiv G).apply_symm_apply v
  have hτ : push (t := ⟨(centralImage G q).map, (centralImage G q).overC⟩)
        (zeroEvaluation G q) (zeroEvaluation_over G q)
        (zeroEvaluation_centre G q) (lift (zeroChart G) z) =
      push (t := ⟨(centralImage G q).map, (centralImage G q).overC⟩)
        j hj hx (lift A (e.differential v.val)) := by
    apply pointLift_ext_general
    change (lift (zeroChart G) z).map ≫ zeroEvaluation G q =
      (lift A (e.differential v.val)).map ≫ j
    rw [he, ← Category.assoc, ← Category.assoc, lift_natural]
    change ((lift G.chart (zeroDirection G z).val).map ≫ e.map) ≫ j = _
    rw [hz, lift_natural]
  rw [AffineIntrinsic.tangentEquiv_pointVector, ← hτ]
  have hv := verticalVariation_value G q z
  rw [hz] at hv
  exact hv.symm

theorem endpointFibre_compatibility
    (b : ProjectiveLine ⟶ CentralFiber G.source)
    (hb : b ≫ centralBase G.source = P.structureMap)
    (f : ProjectiveLine ⟶ X.variety.scheme) (hf : b ≫ centralMap G = f)
    (A : Charts.PointedAffine) (j : A.scheme ⟶ X.variety.scheme)
    [IsOpenImmersion j] (hj : j ≫ X.variety.structureMap = A.toC)
    (hx : A.point.val ≫ j = infinity.map ≫ f)
    (e : Charts.Hom G.chart A)
    (he : zeroEvaluation G (outerBranchPoint G b hb) =
      (zeroChartMap G).map ≫ e.map ≫ j)
    (v : LinearMap.ker G.baseDifferential) :
    endpointFibre G b hb f hf A j hj hx (e.differential v.val) =
      evaluateSection P.structureMap (pullbackModule f (tangentSheaf X.variety.structureMap))
        infinity.map infinity.overC (branchRestriction G b hb f hf (verticalVariation G v)) := by
  let c := LinearEquiv.ofBijective
    (fiberComposition f infinity.map (centralImage G (outerBranchPoint G b hb)).map
      (outerBranchImage G b hb f hf) (tangentSheaf X.variety.structureMap))
    (fiberComposition_bijective f infinity.map (centralImage G (outerBranchPoint G b hb)).map
      (outerBranchImage G b hb f hf) (tangentSheaf X.variety.structureMap))
  apply c.injective
  change c (c.symm (AffineIntrinsic.tangentEquiv A X.variety
    (centralImage G (outerBranchPoint G b hb)) j hj
      (hx.trans (outerBranchImage G b hb f hf)) (e.differential v.val))) = _
  rw [LinearEquiv.apply_symm_apply]
  rw [zeroEvaluation_chart_value G _ A j hj
    (hx.trans (outerBranchImage G b hb f hf)) e he v]
  exact (branchRestriction_value G b hb f hf (verticalVariation G v)).symm

/-- Holding a central point fixed agrees with the marked evaluation
whenever that point is the specialization of the specified section of
the smoothing source. -/
theorem zeroEvaluation_marked
    (q : PointsOver ComplexBase (𝟙 ComplexBase) (CentralFiber G.source)
      (centralBase G.source))
    (m : AffineLine ⟶ G.source.source) (hm : m ≫ G.source.parameter = 𝟙 AffineLine)
    (hqm : q.val ≫ pullback.fst G.source.parameter (scalarPoint 0) = scalarPoint 0 ≫ m) :
    zeroEvaluation G q =
      (zeroChartMap G).map ≫ G.inclusion ≫ markedEvaluation G.hom m hm := by
  have h : zeroEvaluationSource G q =
      (zeroChartMap G).map ≫ G.inclusion ≫
        pullback.lift (G.hom.toBase ≫ m) (𝟙 G.hom.parameter)
          (by simp [Category.assoc, hm]) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, zeroEvaluationSource, pullback.lift_fst,
        pullback.lift_fst_assoc]
      rw [hqm]
      have hc := congrArg (fun k => k ≫ m)
        (pullback.condition (f := G.inclusion ≫ G.hom.toBase) (g := scalarPoint 0))
      simpa only [zeroChart, zeroChartMap, Category.assoc] using hc.symm
    · simp only [Category.assoc, zeroEvaluationSource, pullback.lift_snd,
        pullback.lift_snd_assoc, Category.comp_id]
  simpa only [zeroEvaluation, markedEvaluation, Category.assoc] using
    congrArg (fun k => k ≫ G.hom.evaluation) h

theorem first_zeroEvaluation :
    zeroEvaluation G (outerBranchPoint G (leftBranch G.marks) (leftBranch_over G.marks)) =
      (zeroChartMap G).map ≫ G.firstEval.map ≫ G.firstOpen := by
  have hq : (outerBranchPoint G (leftBranch G.marks) (leftBranch_over G.marks)).val ≫
      pullback.fst G.source.parameter (scalarPoint 0) = scalarPoint 0 ≫ G.marks.first := by
    simpa only [outerBranchPoint, leftBranch, Category.assoc, pullback.lift_fst] using
      (GermProof.first_central G.marks).symm
  rw [zeroEvaluation_marked G _ G.marks.first G.marks.first_base hq,
    ← G.firstEval_spec]

theorem second_zeroEvaluation :
    zeroEvaluation G (outerBranchPoint G (rightBranch G.marks) (rightBranch_over G.marks)) =
      (zeroChartMap G).map ≫ G.secondEval.map ≫ G.secondOpen := by
  have hq : (outerBranchPoint G (rightBranch G.marks) (rightBranch_over G.marks)).val ≫
      pullback.fst G.source.parameter (scalarPoint 0) = scalarPoint 0 ≫ G.marks.second := by
    simpa only [outerBranchPoint, rightBranch, Category.assoc, pullback.lift_fst] using
      (GermProof.second_central G.marks).symm
  rw [zeroEvaluation_marked G _ G.marks.second G.marks.second_base hq,
    ← G.secondEval_spec]

def firstFibre : G.firstTarget.Tangent ≃ₗ[ℂ]
    Fiber (pullbackModule D.first.curve.map (tangentSheaf X.variety.structureMap)) infinity.map := by
  letI : IsOpenImmersion G.firstOpen := G.firstOpen_immersion
  exact endpointFibre G (leftBranch G.marks) (leftBranch_over G.marks)
    D.first.curve.map (centralMap_left G) G.firstTarget G.firstOpen
    G.firstOpen_over G.firstCentre

def secondFibre : G.secondTarget.Tangent ≃ₗ[ℂ]
    Fiber (pullbackModule D.second.curve.map (tangentSheaf X.variety.structureMap)) infinity.map := by
  letI : IsOpenImmersion G.secondOpen := G.secondOpen_immersion
  exact endpointFibre G (rightBranch G.marks) (rightBranch_over G.marks)
    D.second.curve.map (centralMap_right G) G.secondTarget G.secondOpen
    G.secondOpen_over G.secondCentre

theorem firstFibre_compatibility (v : LinearMap.ker G.baseDifferential) :
    firstFibre G (G.verticalEvaluation v).1 =
      outerEvaluation D.first (restrictLeft G (verticalSectionsEquiv G v)) := by
  letI : IsOpenImmersion G.firstOpen := G.firstOpen_immersion
  exact endpointFibre_compatibility G (leftBranch G.marks) (leftBranch_over G.marks)
    D.first.curve.map (centralMap_left G) G.firstTarget G.firstOpen
    G.firstOpen_over G.firstCentre G.firstEval (first_zeroEvaluation G) v

theorem secondFibre_compatibility (v : LinearMap.ker G.baseDifferential) :
    secondFibre G (G.verticalEvaluation v).2 =
      outerEvaluation D.second (restrictRight G (verticalSectionsEquiv G v)) := by
  letI : IsOpenImmersion G.secondOpen := G.secondOpen_immersion
  exact endpointFibre_compatibility G (rightBranch G.marks) (rightBranch_over G.marks)
    D.second.curve.map (centralMap_right G) G.secondTarget G.secondOpen
    G.secondOpen_over G.secondCentre G.secondEval (second_zeroEvaluation G) v

/-- The complete comparison retains both actual endpoint maps and the
actual universal-family section map. -/
def comparison : RelativeTangentComparison G where
  verticalSections := verticalSectionsEquiv G
  firstFibre := firstFibre G
  secondFibre := secondFibre G
  endpointCompatibility := by
    intro v
    exact Prod.ext (firstFibre_compatibility G v) (secondFibre_compatibility G v)

end LeBrunSalamon.Construction.Normalization.NodalTangent

namespace LeBrunSalamon.Construction.Normalization

open Smoothing Lines

/-- Before constructing this diagram, normalize firstFibre and secondFibre
by point derivations/differentials on their affine charts, and normalize
verticalSections using square-zero lifts of the universal evaluation.
The existence theorem asserts only the required diagram, not arbitrary
normalizations or uniqueness of every displayed equivalence. -/
theorem relativeTangentComparison_exists {n : ℕ} {X : ContactFanoManifold n}
    {D : SuitablePair X} (G : Germ D) : Nonempty (RelativeTangentComparison G) := by
  exact ⟨NodalTangent.comparison G⟩

end LeBrunSalamon.Construction.Normalization

namespace LeBrunSalamon.Construction.Smoothing

open Lines

/-- Source sm:vertical-cokernel. Prove using the normalization sequence,
endpoint vanishing, and D.spans. This is not a dimension-only assumption. -/
theorem germ_verticalDefectOne {n : ℕ} {X : ContactFanoManifold n}
    {D : SuitablePair X} (G : Germ D) : G.VerticalDefectOne := by
  obtain ⟨T⟩ := Normalization.relativeTangentComparison_exists G
  exact Normalization.relativeTangentComparison_defectOne G T

end LeBrunSalamon.Construction.Smoothing

end

#print axioms LeBrunSalamon.Construction.Normalization.relativeTangentComparison_exists
