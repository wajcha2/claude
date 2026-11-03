import LSHomVelocity
import LSProjectionFormula
import LSDualStructureExact
import LSTensorLocallyFreeExact

/-!
# The exact-sequence step in dual-thickening Hom vanishing

This file contains no new admission.  The generic exact-sequence argument
is applied to the actual structure-sheaf epsilon extension. Tensor
exactness is the literal generic EGA I (0, 5.4.1) input; the epsilon and
Hom translations are proved below.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 300000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton LeBrunSalamon.Construction

namespace LeBrunSalamon.DualHomVanishing

theorem hom_zero_of_shortExact {X : Scheme} {A B C D : OModule X}
    (f : A ⟶ B) (g : B ⟶ C) (hfg : f ≫ g = 0)
    (hex : (ShortComplex.mk f g hfg).ShortExact)
    (hA : ∀ a : D ⟶ A, a = 0) (hC : ∀ c : D ⟶ C, c = 0)
    (m : D ⟶ B) : m = 0 := by
  obtain ⟨a, ha⟩ := KernelFork.IsLimit.lift' hex.fIsKernel m (hC (m ≫ g))
  change a ≫ f = m at ha
  simpa only [hA a, zero_comp] using ha.symm

/-- Adjunction and the actual retraction identify maps to a pushed
reduction with maps from the original E to the original reduced F. -/
theorem hom_to_reduction_zero {X Y : Scheme} (p : X ⟶ Y) (i : Y ⟶ X)
    (hi : i ≫ p = 𝟙 Y) (E : OModule Y) (F : OModule X)
    (h : ∀ m : E ⟶ pullbackModule i F, m = 0)
    (n : pullbackModule p E ⟶
      (Scheme.Modules.pushforward i).obj (pullbackModule i F)) : n = 0 := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction i
  let e : pullbackModule i (pullbackModule p E) ≅ E :=
    compositionPullback i p (𝟙 Y) hi E ≪≫ (Scheme.Modules.pullbackId Y).app E
  let v := (adj.homEquiv _ _).symm n
  have hv : v = 0 := by
    apply (cancel_epi e.inv).mp
    simpa only [comp_zero] using h (e.inv ≫ v)
  apply (adj.homEquiv _ _).symm.injective
  rw [show (adj.homEquiv _ _).symm n = v from rfl, hv]
  simp only [Adjunction.homEquiv_symm_apply, Functor.map_zero, zero_comp]

/-- The actual projection formula supplies the two end terms after
tensoring the structure-sheaf epsilon extension.  No family, contact,
or Hom-vanishing assertion is part of the imported projection-formula
leaf. -/
theorem hom_vanishing_of_structure_extension
    {X Y : Scheme} (p : X ⟶ Y) (i : Y ⟶ X) (hi : i ≫ p = 𝟙 Y)
    {q : ℕ} (E : OModule Y) (F : AlgebraicVectorBundle X q)
    (j : (Scheme.Modules.pushforward i).obj (structureModule Y) ⟶ structureModule X)
    (hj : j ≫ structurePushforwardMap i = 0)
    (hex : ((ShortComplex.mk j (structurePushforwardMap i) hj).map
      (tensorLeftFunctor F.sheaf)).ShortExact)
    (h : ∀ m : E ⟶ pullbackModule i F.sheaf, m = 0)
    (m : pullbackModule p E ⟶ F.sheaf) : m = 0 := by
  obtain ⟨t, ht, hr⟩ := F.locallyFree
  letI := ht
  have hfinite (a : t.I) : Finite (t.generators a).I :=
    Finite.of_equiv (Fin q) (Classical.choice (hr a)).symm
  letI := PublishedInputs.ProjectionFormula.canonicalMap_isIso i F.sheaf
    (structureModule Y) t hfinite
  let e : tensorSheaf F.sheaf ((Scheme.Modules.pushforward i).obj (structureModule Y)) ≅
      (Scheme.Modules.pushforward i).obj (pullbackModule i F.sheaf) :=
    asIso (ProjectionFormulaProof.canonicalMap i F.sheaf (structureModule Y)) ≪≫
      (Scheme.Modules.pushforward i).mapIso
        (TensorConstruction.rightUnitIso (pullbackModule i F.sheaf))
  have hend (a : pullbackModule p E ⟶
      tensorSheaf F.sheaf ((Scheme.Modules.pushforward i).obj (structureModule Y))) :
      a = 0 := by
    apply (cancel_mono e.hom).mp
    simpa only [zero_comp] using hom_to_reduction_zero p i hi E F.sheaf h (a ≫ e.hom)
  let S := (ShortComplex.mk j (structurePushforwardMap i) hj).map
    (tensorLeftFunctor F.sheaf)
  have hm : m ≫ (TensorConstruction.rightUnitIso F.sheaf).inv = 0 :=
    hom_zero_of_shortExact S.f S.g S.zero hex hend hend
      (m ≫ (TensorConstruction.rightUnitIso F.sheaf).inv)
  apply (cancel_mono (TensorConstruction.rightUnitIso F.sheaf).inv).mp
  simpa only [zero_comp] using hm

/-- Vanishing on the original reduction kills a Hom on the actual
trivial dual thickening. Both filtration terms are compared by the
canonical projection formula and the actual retraction. -/
theorem dualThickening_hom_vanishing {Y : Scheme} (sY : Y ⟶ ComplexBase)
    {r q : ℕ} (E : AlgebraicVectorBundle Y r)
    (F : AlgebraicVectorBundle (Lines.DualThickening.space sY) q)
    (h : ∀ m : E.sheaf ⟶ pullbackModule (Lines.DualThickening.zeroSection sY) F.sheaf,
      m = 0)
    (m : pullbackModule (Lines.DualThickening.projection sY) E.sheaf ⟶ F.sheaf) :
    m = 0 := by
  let S := ShortComplex.mk (epsilonInjection sY)
    (structurePushforwardMap (Lines.DualThickening.zeroSection sY))
    (epsilonInjection_reduction sY)
  have hS : (S.map (tensorLeftFunctor F.sheaf)).ShortExact :=
    PublishedInputs.TensorExactness.locallyFree_tensor_shortExact
      F.sheaf F.locallyFree S (epsilon_structure_shortExact sY)
  exact hom_vanishing_of_structure_extension
    (Lines.DualThickening.projection sY) (Lines.DualThickening.zeroSection sY)
    (Lines.DualThickening.zeroSection_projection sY) E.sheaf F
    (epsilonInjection sY) (epsilonInjection_reduction sY) hS h m

end LeBrunSalamon.DualHomVanishing
end
