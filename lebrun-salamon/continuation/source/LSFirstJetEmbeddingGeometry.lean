import LSFirstJetEmbedding
import LSHamiltonianJets

/-!
# Closed projective embeddings separate the actual first jets

The geometric argument tests the universal projective quotient on the
dual-number scheme. A radial first derivative changes its coordinate
tuple by the unit 1 + epsilon * k. The universal property identifies the
projective morphisms, and the closed immersion is a monomorphism.

All pullback frames below are normalized by their original coefficients.
No statement in this file is admitted. Kernel replay is pending.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseFour LeBrunSalamon.PhaseSeven
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentySeven LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Core LeBrunSalamon.Skeleton
open LeBrunSalamon.Refinement LeBrunSalamon.Refinement.Jets
open LeBrunSalamon.Construction

namespace LeBrunSalamon.ClassicalReduction.FirstJetProof

namespace AffineTestFrame

open PointFrame.LocalFrameJetProof

variable {Y T : Scheme} {L : LineBundle Y}

def scalarSection (r : RingSections T ⊤) : AlgebraicSection (structureModule T) :=
  sectionFromValue r

theorem scalarSection_eq_scalarEnd (r : RingSections T ⊤) :
    scalarSection r = GlobalScalars.scalarEnd (structureModule T) r := by
  apply (sectionValue_bijective (structureModule T)).injective
  rw [scalarSection, sectionFromValue_spec]
  change r = (GlobalScalars.scalarEnd (structureModule T) r).app ⊤
    (1 : RingSections T ⊤)
  simp [GlobalScalars.scalarEnd_app, smul_eq_mul]

theorem scalarSection_mul (a b : RingSections T ⊤) :
    scalarSection (a * b) = scalarSection a ≫ scalarSection b := by
  simp only [scalarSection_eq_scalarEnd, GlobalScalars.scalarEnd_mul]

def coefficient (H : AffineLineFrame L) (f : T ⟶ Y)
    (hU : ⊤ ≤ f ⁻¹ᵁ H.openSet) :
    GlobalSections (pullbackModule f L.sheaf) ≃ₗ[RingSections T ⊤]
      RingSections T ⊤ := coefficientOn H f ⊤ hU

def frameSection (H : AffineLineFrame L) (f : T ⟶ Y)
    (hU : ⊤ ≤ f ⁻¹ᵁ H.openSet) :
    AlgebraicSection (pullbackModule f L.sheaf) :=
  sectionFromValue ((coefficient H f hU).symm 1)

theorem frameSection_apply (H : AffineLineFrame L) (f : T ⟶ Y)
    (hU : ⊤ ≤ f ⁻¹ᵁ H.openSet) (a : RingSections T ⊤) :
    (frameSection H f hU).app ⊤ a = (coefficient H f hU).symm a := by
  have h1 : (frameSection H f hU).app ⊤ (1 : RingSections T ⊤) =
      (coefficient H f hU).symm 1 := sectionFromValue_spec _
  calc
    _ = a • (frameSection H f hU).app ⊤ (1 : RingSections T ⊤) := by
      simpa only [smul_eq_mul, mul_one] using
        ((frameSection H f hU).app ⊤).hom.map_smul a (1 : RingSections T ⊤)
    _ = _ := by
      rw [h1, ← (coefficient H f hU).symm.map_smul]
      simp only [smul_eq_mul, mul_one]

theorem frameSection_isIso [IsAffine T] (H : AffineLineFrame L) (f : T ⟶ Y)
    (hU : ⊤ ≤ f ⁻¹ᵁ H.openSet) : IsIso (frameSection H f hU) := by
  letI : (structureModule T).IsQuasicoherent :=
    LocalExtensionSplitting.quasicoherent_of_locallyFreeRank (structureModule_rank T)
  letI : (pullbackModule f L.sheaf).IsQuasicoherent :=
    LocalExtensionSplitting.quasicoherent_of_locallyFreeRank (pullbackLine f L).locallyFree
  apply affine_isIso_of_appTop_bijective
  constructor
  · intro a b h
    exact (coefficient H f hU).symm.injective
      ((frameSection_apply H f hU a).symm.trans (h.trans (frameSection_apply H f hU b)))
  · intro a
    exact ⟨coefficient H f hU a, by
      rw [frameSection_apply, (coefficient H f hU).symm_apply_apply]⟩

def iso [IsAffine T] (H : AffineLineFrame L) (f : T ⟶ Y)
    (hU : ⊤ ≤ f ⁻¹ᵁ H.openSet) :
    pullbackModule f L.sheaf ≅ structureModule T := by
  letI := frameSection_isIso H f hU
  exact (asIso (frameSection H f hU)).symm

theorem iso_apply [IsAffine T] (H : AffineLineFrame L) (f : T ⟶ Y)
    (hU : ⊤ ≤ f ⁻¹ᵁ H.openSet) (a : GlobalSections (pullbackModule f L.sheaf)) :
    (iso H f hU).hom.app ⊤ a = coefficient H f hU a := by
  letI := frameSection_isIso H f hU
  have h := congrArg (fun q : structureModule T ⟶ structureModule T =>
    q.app ⊤ (coefficient H f hU a)) (asIso (frameSection H f hU)).hom_inv_id
  change (iso H f hU).hom.app ⊤
    ((frameSection H f hU).app ⊤ (coefficient H f hU a)) = coefficient H f hU a at h
  rw [frameSection_apply, (coefficient H f hU).symm_apply_apply] at h
  exact h

theorem iso_section [IsAffine T] (H : AffineLineFrame L) (f : T ⟶ Y)
    (hU : ⊤ ≤ f ⁻¹ᵁ H.openSet) (a : AlgebraicSection L.sheaf) :
    pullSection f a ≫ (iso H f hU).hom =
      scalarSection (f.appLE H.openSet ⊤ hU (H.localCoefficient a)) := by
  apply (sectionValue_bijective (structureModule T)).injective
  rw [sectionValue_comp, iso_apply]
  change coefficient H f hU (sectionValue (pullSection f a)) = _
  simpa only [scalarSection, sectionFromValue_spec, homOfLE_refl, op_id,
    CategoryTheory.Functor.map_id, ModuleCat.id_apply] using
    coefficientOn_global H f ⊤ hU a

end AffineTestFrame

namespace PointFrameDual

variable {d : ℕ} {X : SmoothProperComplexVariety d} {L : LineBundle X.scheme}
  {x : ComplexPoint X} (F : PointFrame X L x)

def chart : Charts.PointedAffine where
  scheme := F.frame.openSet.toScheme
  affine := F.frame.isAffine
  toC := F.frame.openSet.ι ≫ X.structureMap
  point := ⟨F.pointLift, by rw [← Category.assoc, F.overPoint, x.overC]⟩

/-- The original affine coordinate ring and the chart's global ring differ
by the canonical open-subscheme comparison, which respects complex constants. -/
def chartRingIso : F.ChartRing ≃ₐ[ℂ] (chart F).Ring where
  toRingEquiv := F.frame.openSet.topIso.commRingCatIsoToRingEquiv.symm
  commutes' := by
    intro c
    change F.frame.openSet.topIso.inv (complexConstant X.structureMap F.frame.openSet c) =
      complexConstants (F.frame.openSet.ι ≫ X.structureMap) c
    rw [complexConstants_apply_top, Scheme.Hom.comp_appTop]
    exact ScalarSections.topIso_inv_restrict F.frame.openSet
      (X.structureMap.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))

theorem evaluation_chartRingIso (a : F.ChartRing) :
    (chart F).evaluation (chartRingIso F a) = F.evaluation a := rfl

theorem evaluation_chartRingIso_symm (a : (chart F).Ring) :
    F.evaluation ((chartRingIso F).symm a) = (chart F).evaluation a := by
  rw [← evaluation_chartRingIso, (chartRingIso F).apply_symm_apply]

def tangent (D : F.Tangent) : (chart F).Tangent :=
  ⟨D.val.comp (chartRingIso F).symm.toLinearMap, by
    intro a b
    change D.val ((chartRingIso F).symm (a * b)) =
      (chart F).evaluation a * D.val ((chartRingIso F).symm b) +
      (chart F).evaluation b * D.val ((chartRingIso F).symm a)
    rw [map_mul, D.property, evaluation_chartRingIso_symm,
      evaluation_chartRingIso_symm]⟩

theorem tangent_injective : Function.Injective (tangent F) := by
  intro D E h
  apply Subtype.ext
  apply LinearMap.ext
  intro a
  have h' := congrArg (fun D : (chart F).Tangent => D.val (chartRingIso F a)) h
  change D.val ((chartRingIso F).symm (chartRingIso F a)) =
    E.val ((chartRingIso F).symm (chartRingIso F a)) at h'
  simpa only [(chartRingIso F).symm_apply_apply] using h'

def lift (D : F.Tangent) :
    Infinitesimal.PointLift (chart F).scheme (chart F).toC (chart F).point :=
  (chart F).tangentLiftEquiv (tangent F D)

def map (D : F.Tangent) : Infinitesimal.DualScheme ⟶ X.scheme :=
  (lift F D).map ≫ F.frame.openSet.ι

theorem overC (D : F.Tangent) : map F D ≫ X.structureMap = Infinitesimal.dualToC := by
  change ((lift F D).map ≫ F.frame.openSet.ι) ≫ X.structureMap = _
  rw [Category.assoc]
  exact (lift F D).overC

theorem map_injective : Function.Injective (map F) := by
  intro D E h
  apply tangent_injective F
  apply (chart F).tangentLiftEquiv.injective
  have hm : (lift F D).map = (lift F E).map :=
    (cancel_mono F.frame.openSet.ι).mp h
  have hext {a b : Infinitesimal.PointLift (chart F).scheme (chart F).toC (chart F).point}
      (hab : a.map = b.map) : a = b := by
    cases a
    cases b
    cases hab
    rfl
  exact hext hm

def support (D : F.Tangent) : ⊤ ≤ map F D ⁻¹ᵁ F.frame.openSet := by
  intro z hz
  exact ((lift F D).map z).property

theorem openFactor_appLE {Y T : Scheme} (U : Y.Opens)
    (q : T ⟶ U.toScheme) (hU : ⊤ ≤ (q ≫ U.ι) ⁻¹ᵁ U) :
    (q ≫ U.ι).appLE U ⊤ hU = U.topIso.inv ≫ q.appTop := by
  have hι : U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
    simp only [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appLE] <;> congr 1
  have h := Scheme.Hom.appLE_comp_appLE q U.ι U ⊤ ⊤ U.ι_preimage_self.ge le_rfl
  rw [hι] at h
  exact h.symm.trans (congrArg (fun k => U.topIso.inv ≫ k)
    (Scheme.Hom.appLE_eq_app q (U := ⊤)))

/-- The infinitesimal test map sends every original local function to its
actual value plus epsilon times the specified point derivation. -/
theorem appLE (D : F.Tangent) (a : F.ChartRing) :
    (map F D).appLE F.frame.openSet ⊤ (support F D) a =
      (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv
        (algebraMap ℂ Infinitesimal.Dual (F.evaluation a) +
          Infinitesimal.epsilon * algebraMap ℂ Infinitesimal.Dual (D.val a)) := by
  rw [map, openFactor_appLE]
  change ((chart F).tangentLiftEquiv (tangent F D)).map.appTop (chartRingIso F a) = _
  rw [(chart F).tangentLiftEquiv_normalized]
  change (Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv
    (algebraMap ℂ Infinitesimal.Dual ((chart F).evaluation (chartRingIso F a)) +
      Infinitesimal.epsilon * algebraMap ℂ Infinitesimal.Dual
        (D.val ((chartRingIso F).symm (chartRingIso F a)))) = _
  rw [evaluation_chartRingIso, (chartRingIso F).symm_apply_apply]

def frameIso (D : F.Tangent) :
    pullbackModule (map F D) L.sheaf ≅ structureModule Infinitesimal.DualScheme :=
  AffineTestFrame.iso F.frame (map F D) (support F D)

theorem frameIso_section (D : F.Tangent) (a : AlgebraicSection L.sheaf) :
    pullSection (map F D) a ≫ (frameIso F D).hom =
      AffineTestFrame.scalarSection
        ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv
          (algebraMap ℂ Infinitesimal.Dual (F.evaluation (F.coefficient a)) +
            Infinitesimal.epsilon * algebraMap ℂ Infinitesimal.Dual
              (D.val (F.coefficient a)))) := by
  rw [frameIso, AffineTestFrame.iso_section, appLE]

end PointFrameDual

namespace DualCoordinateProof

open Infinitesimal

/-- The first-order radial change is an actual unit, with its inverse
specified algebraically using epsilon squared equal to zero. -/
def radialUnit (k : ℂ) : Dualˣ where
  val := 1 + epsilon * algebraMap ℂ Dual k
  inv := 1 - epsilon * algebraMap ℂ Dual k
  val_inv := by ring_nf; simp [epsilon_square]
  inv_val := by ring_nf; simp [epsilon_square]

def radialUnitGlobal (k : ℂ) : (RingSections DualScheme ⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of Dual)).inv.hom.toMonoidHom (radialUnit k)

theorem radial_formula (a k : ℂ) :
    algebraMap ℂ Dual a + epsilon * algebraMap ℂ Dual (k * a) =
      algebraMap ℂ Dual a * (radialUnit k).val := by
  simp only [radialUnit, map_mul]
  ring

theorem radial_section (a k : ℂ) :
    AffineTestFrame.scalarSection ((Scheme.ΓSpecIso (CommRingCat.of Dual)).inv
      (algebraMap ℂ Dual a + epsilon * algebraMap ℂ Dual (k * a))) =
    AffineTestFrame.scalarSection ((Scheme.ΓSpecIso (CommRingCat.of Dual)).inv
      (algebraMap ℂ Dual a)) ≫
      (GlobalScalars.scalarIso (structureModule DualScheme) (radialUnitGlobal k)).hom := by
  rw [radial_formula, map_mul, AffineTestFrame.scalarSection_mul]
  congr 1
  exact AffineTestFrame.scalarSection_eq_scalarEnd _

/-- Coordinate frames may differ by a global unit without changing the
projective morphism, on nonreduced test schemes as well. -/
theorem projectiveMaps_eq_of_scaled_frames {T : Scheme} {N : ℕ}
    (P : ProjectiveCoordinates N) (sT : T ⟶ ComplexBase)
    (f g : PointsOver T sT (ComplexProjectiveSpace N) (projectiveBaseMap N))
    (ef : pullbackModule f.val P.hyperplane.sheaf ≅ structureModule T)
    (eg : pullbackModule g.val P.hyperplane.sheaf ≅ structureModule T)
    (u : (RingSections T ⊤)ˣ)
    (h : ∀ i, pullSection f.val (P.coordinate i) ≫ ef.hom =
      pullSection g.val (P.coordinate i) ≫ eg.hom ≫
        (GlobalScalars.scalarIso (structureModule T) u).hom) : f = g := by
  let e := eg ≪≫ GlobalScalars.scalarIso (structureModule T) u ≪≫ ef.symm
  apply projectiveMaps_eq_of_coordinateIso P sT f g e
  intro i
  apply (cancel_mono ef.hom).mp
  simpa only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    ef.inv_hom_id, Category.comp_id] using (h i).symm

end DualCoordinateProof

/-- Compose the actual line polarization with a specified frame after
pullback. The comparison is the canonical pullback-composition isomorphism. -/
def compositeFrame {Y Z T : Scheme} (f : Y ⟶ Z) (g : T ⟶ Y)
    (M : LineBundle Z) (L : LineBundle Y)
    (e : pullbackModule f M.sheaf ≅ L.sheaf)
    (c : pullbackModule g L.sheaf ≅ structureModule T) :
    pullbackModule (g ≫ f) M.sheaf ≅ structureModule T :=
  ((Scheme.Modules.pullbackComp g f).app M.sheaf).symm ≪≫
    (Scheme.Modules.pullback g).mapIso e ≪≫ c

theorem compositeFrame_section {Y Z T : Scheme} (f : Y ⟶ Z) (g : T ⟶ Y)
    (M : LineBundle Z) (L : LineBundle Y)
    (e : pullbackModule f M.sheaf ≅ L.sheaf)
    (c : pullbackModule g L.sheaf ≅ structureModule T)
    (a : AlgebraicSection M.sheaf) :
    pullSection (g ≫ f) a ≫ (compositeFrame f g M L e c).hom =
      pullSection g (pullSection f a ≫ e.hom) ≫ c.hom := by
  let p := (Scheme.Modules.pullbackComp g f).app M.sheaf
  change pullSection (g ≫ f) a ≫
    (p.inv ≫ (Scheme.Modules.pullback g).map e.hom ≫ c.hom) = _
  rw [← CanonicalPullbackSectionProof.pullSection_comp]
  change (pullSection g (pullSection f a) ≫ p.hom) ≫
    (p.inv ≫ (Scheme.Modules.pullback g).map e.hom ≫ c.hom) = _
  simp only [Category.assoc, p.hom_inv_id_assoc]
  rw [ExternalExchangeCoherenceProof.pullSection_map, Category.assoc]

namespace Embedding

variable {d N : ℕ} {X : SmoothProperComplexVariety d} {L : LineBundle X.scheme}
  (P : ProjectiveCoordinates N) (f : X.scheme ⟶ ComplexProjectiveSpace N)
  (e : pullbackModule f P.hyperplane.sheaf ≅ L.sheaf)

def sections : Fin (N + 1) → AlgebraicSection L.sheaf :=
  fun i => pullSection f (P.coordinate i) ≫ e.hom

/-- Generating projective coordinates have a nonzero value tuple in the
specified line frame. This uses generation only at this stage. -/
theorem tupleJet_value_ne_zero {x : ComplexPoint X} (F : PointFrame X L x) :
    (tupleJet F (sections P f e)).value ≠ 0 := by
  let p := x.map ≫ f
  let c := compositeFrame f x.map P.hyperplane L e F.lineFiberFrameIso
  have hc (i : Fin (N + 1)) :
      pullSection p (P.coordinate i) ≫ c.hom =
        scalarUnitSection ((tupleJet F (sections P f e)).value i) := by
    exact (compositeFrame_section f x.map P.hyperplane L e
      F.lineFiberFrameIso (P.coordinate i)).trans
        (F.lineFiberFrameIso_section (sections P f e i))
  have hg := ProjectiveCoordinateProof.pulled_tuple_generates P.hyperplane
    P.coordinate P.generates p c
  have ht : (fun i => pullSection p (P.coordinate i) ≫ c.hom) =
      (fun i => scalarUnitSection ((tupleJet F (sections P f e)).value i)) :=
    funext hc
  rw [ht] at hg
  exact ProjectiveCoordinateProof.scalar_tuple_ne_zero _ hg

def dualPoint (hf : f ≫ projectiveBaseMap N = X.structureMap)
    {x : ComplexPoint X} (F : PointFrame X L x) (D : F.Tangent) :
    PointsOver Infinitesimal.DualScheme Infinitesimal.dualToC
      (ComplexProjectiveSpace N) (projectiveBaseMap N) :=
  ⟨PointFrameDual.map F D ≫ f, by
    rw [Category.assoc, hf, PointFrameDual.overC]⟩

def dualFrame {x : ComplexPoint X} (F : PointFrame X L x) (D : F.Tangent) :
    pullbackModule (PointFrameDual.map F D ≫ f) P.hyperplane.sheaf ≅
      structureModule Infinitesimal.DualScheme :=
  compositeFrame f (PointFrameDual.map F D) P.hyperplane L e
    (PointFrameDual.frameIso F D)

theorem dualFrame_coordinate {x : ComplexPoint X}
    (F : PointFrame X L x) (D : F.Tangent) (i : Fin (N + 1)) :
    pullSection (PointFrameDual.map F D ≫ f) (P.coordinate i) ≫
      (dualFrame P f e F D).hom =
    AffineTestFrame.scalarSection
      ((Scheme.ΓSpecIso (CommRingCat.of Infinitesimal.Dual)).inv
        (algebraMap ℂ Infinitesimal.Dual (F.evaluation (F.coefficient (sections P f e i))) +
          Infinitesimal.epsilon * algebraMap ℂ Infinitesimal.Dual
            (D.val (F.coefficient (sections P f e i))))) := by
  exact (compositeFrame_section f (PointFrameDual.map F D) P.hyperplane L e
    (PointFrameDual.frameIso F D) (P.coordinate i)).trans
      (PointFrameDual.frameIso_section F D (sections P f e i))

/-- A projective embedding has no radial tangent kernel. The argument
uses the full universal property on the actual dual-number scheme and
the monomorphism of the actual embedding. -/
theorem tupleJet_projectivelyImmersive [Mono f]
    (hf : f ≫ projectiveBaseMap N = X.structureMap)
    {x : ComplexPoint X} (F : PointFrame X L x) :
    (tupleJet F (sections P f e)).IsProjectivelyImmersive := by
  refine ⟨tupleJet_value_ne_zero P f e F, ?_⟩
  intro D k hD
  apply PointFrameDual.map_injective F
  apply (cancel_mono f).mp
  have hmaps := DualCoordinateProof.projectiveMaps_eq_of_scaled_frames P
    Infinitesimal.dualToC (dualPoint f hf F D) (dualPoint f hf F 0)
    (dualFrame P f e F D) (dualFrame P f e F 0)
    (DualCoordinateProof.radialUnitGlobal k) (by
      intro i
      change pullSection (PointFrameDual.map F D ≫ f) (P.coordinate i) ≫
          (dualFrame P f e F D).hom =
        pullSection (PointFrameDual.map F 0 ≫ f) (P.coordinate i) ≫
          (dualFrame P f e F 0).hom ≫ _
      rw [← Category.assoc, dualFrame_coordinate, dualFrame_coordinate]
      have hi : D.val (F.coefficient (sections P f e i)) =
          k * F.evaluation (F.coefficient (sections P f e i)) := congrFun hD i
      rw [hi]
      simpa only [Submodule.coe_zero, LinearMap.zero_apply, map_zero, mul_zero,
        add_zero] using
        DualCoordinateProof.radial_section
          (F.evaluation (F.coefficient (sections P f e i))) k)
  exact congrArg Subtype.val hmaps

end Embedding

/-- The pullback of a universal projective quotient along an actual
closed immersion separates the existing scheme-theoretic first jets.
All section formation, local frame comparisons and infinitesimal tests
are constructed above; no very-ampleness or jet theorem is admitted. -/
theorem projectiveEmbedding_firstJets {d N : ℕ}
    (X : SmoothProperComplexVariety d) (L : LineBundle X.scheme)
    (P : ProjectiveCoordinates N) (f : X.scheme ⟶ ComplexProjectiveSpace N)
    (hclosed : IsClosedImmersion f)
    (hf : f ≫ projectiveBaseMap N = X.structureMap)
    (e : pullbackModule f P.hyperplane.sheaf ≅ L.sheaf) :
    SeparatesFirstJets X L := by
  letI : IsClosedImmersion f := hclosed
  intro x
  obtain ⟨F⟩ := pointFrame_exists X L x
  exact separatesJetsAt_of_tuple_immersive F (Embedding.sections P f e)
    (Embedding.tupleJet_projectivelyImmersive P f e hf F)

end LeBrunSalamon.ClassicalReduction.FirstJetProof

end
