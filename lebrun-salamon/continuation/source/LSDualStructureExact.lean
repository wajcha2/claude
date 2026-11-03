import LSEpsilonStructureSequence
import LSSheafSectionExact

/-!
# The epsilon kernel as an actual module sheaf

All open-set maps use the actual source projection and zero section.
The only geometric input is the already-proved dual-thickening normal
form; this file contains no new admission.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 300000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton
open LeBrunSalamon.Construction.Lines.DualThickening

namespace LeBrunSalamon.DualHomVanishing

variable {Y : Scheme} (sY : Y ⟶ ComplexBase)

@[simp] theorem projection_preimage_zeroSection (U : (space sY).Opens) :
    projection sY ⁻¹ᵁ (zeroSection sY ⁻¹ᵁ U) = U := by
  ext x
  change zeroSection sY (projection sY x) ∈ U ↔ x ∈ U
  rw [zeroSection_projection_apply]

/-- Pull a function back along p, restricting to the original open. -/
def liftRing (U : (space sY).Opens) :
    Y.presheaf.obj (op (zeroSection sY ⁻¹ᵁ U)) ⟶ (space sY).presheaf.obj (op U) :=
  (projection sY).appLE (zeroSection sY ⁻¹ᵁ U) U
    (projection_preimage_zeroSection sY U).ge

def epsilonAt (U : (space sY).Opens) : RingSections (space sY) U :=
  (space sY).presheaf.map (homOfLE le_top).op
    ((parameter sY).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of LeBrunSalamon.Construction.Infinitesimal.Dual)).inv
        LeBrunSalamon.Construction.Infinitesimal.epsilon))

def normalFormAt (U : (space sY).Opens)
    (a b : RingSections Y (zeroSection sY ⁻¹ᵁ U)) : RingSections (space sY) U :=
  liftRing sY U a + epsilonAt sY U * liftRing sY U b

/-- Transport only the open set; both coefficients and both scheme maps
remain the prescribed ones. -/
theorem normalFormAt_unique (U : (space sY).Opens) (z : RingSections (space sY) U) :
    ∃! ab : RingSections Y (zeroSection sY ⁻¹ᵁ U) ×
      RingSections Y (zeroSection sY ⁻¹ᵁ U), z = normalFormAt sY U ab.1 ab.2 := by
  let V := zeroSection sY ⁻¹ᵁ U
  let hU : projection sY ⁻¹ᵁ V = U := projection_preimage_zeroSection sY U
  let e := (space sY).presheaf.mapIso (eqToIso (congrArg op hU))
  have he : e.hom = (space sY).presheaf.map (homOfLE hU.ge).op := by
    congr 1
  have hl (a : RingSections Y V) : e.hom ((projection sY).app V a) = liftRing sY U a := by
    have h : (projection sY).app V ≫ e.hom = liftRing sY U := by
      rw [he, (projection sY).app_eq_appLE, Scheme.Hom.appLE_map]
      rfl
    exact congrArg (fun k => k a) h
  have hε : e.hom (epsilonOn sY V) = epsilonAt sY U := by
    rw [he]
    unfold epsilonOn epsilonAt
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  have hn (a b : RingSections Y V) :
      e.hom (normalForm sY V a b) = normalFormAt sY U a b := by
    simp only [normalForm, normalFormAt, map_add, map_mul, hl, hε]
  obtain ⟨ab, hab, huniq⟩ :=
    LeBrunSalamon.Construction.StandardInputs.InfinitesimalGeometry.dualThickening_normalForm_unique
      sY V (e.inv z)
  refine ⟨ab, ?_, ?_⟩
  · have h := congrArg e.hom hab
    simpa only [← CommRingCat.comp_apply, e.inv_hom_id, CommRingCat.id_apply, hn] using h
  · intro cd hcd
    apply huniq
    apply (ConcreteCategory.bijective_of_isIso e.hom).injective
    rw [hn]
    change e.hom (e.inv z) = normalFormAt sY U cd.1 cd.2
    simpa only [← CommRingCat.comp_apply, e.inv_hom_id, CommRingCat.id_apply] using hcd

theorem reduction_liftRing (U : (space sY).Opens)
    (a : RingSections Y (zeroSection sY ⁻¹ᵁ U)) :
    (zeroSection sY).app U (liftRing sY U a) = a := by
  have h : liftRing sY U ≫ (zeroSection sY).app U =
      𝟙 (Y.presheaf.obj (op (zeroSection sY ⁻¹ᵁ U))) := by
    rw [(zeroSection sY).app_eq_appLE]
    unfold liftRing
    rw [Scheme.Hom.appLE_comp_appLE]
    rw [appLE_of_map_eq (zeroSection_projection sY) _ _ _ (by simp)]
    simp [Scheme.Hom.appLE]
    exact Y.presheaf.map_id (op (zeroSection sY ⁻¹ᵁ U))
  exact congrArg (fun k => k a) h

theorem reduction_epsilonAt (U : (space sY).Opens) :
    (zeroSection sY).app U (epsilonAt sY U) = 0 := by
  have hres : (space sY).presheaf.map (homOfLE le_top).op ≫ (zeroSection sY).app U =
      (zeroSection sY).appTop ≫ Y.presheaf.map (homOfLE le_top).op := by
    rw [(zeroSection sY).app_eq_appLE, Scheme.Hom.map_appLE]
    rw [show (zeroSection sY).appTop = (zeroSection sY).appLE ⊤ ⊤ le_rfl by
      simp [Scheme.Hom.appLE], Scheme.Hom.appLE_map]
  have hz : (zeroSection sY).appTop
      ((parameter sY).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of LeBrunSalamon.Construction.Infinitesimal.Dual)).inv
          LeBrunSalamon.Construction.Infinitesimal.epsilon)) = 0 := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, zeroSection_parameter,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply, origin_epsilon, map_zero]
  unfold epsilonAt
  rw [← CommRingCat.comp_apply, hres, CommRingCat.comp_apply, hz, map_zero]

theorem reduction_normalFormAt (U : (space sY).Opens)
    (a b : RingSections Y (zeroSection sY ⁻¹ᵁ U)) :
    (zeroSection sY).app U (normalFormAt sY U a b) = a := by
  simp only [normalFormAt, map_add, map_mul, reduction_liftRing,
    reduction_epsilonAt, zero_mul, add_zero]

def epsilonInclusionAt (U : (space sY).Opens)
    (a : RingSections Y (zeroSection sY ⁻¹ᵁ U)) : RingSections (space sY) U :=
  epsilonAt sY U * liftRing sY U a

theorem epsilonInclusionAt_normalFormAt (U : (space sY).Opens)
    (a : RingSections Y (zeroSection sY ⁻¹ᵁ U)) :
    epsilonInclusionAt sY U a = normalFormAt sY U 0 a := by
  simp only [epsilonInclusionAt, normalFormAt, map_zero, zero_add]

theorem epsilonInclusionAt_injective (U : (space sY).Opens) :
    Function.Injective (epsilonInclusionAt sY U) := by
  intro a b hab
  obtain ⟨ab, hab', hu⟩ := normalFormAt_unique sY U (epsilonInclusionAt sY U a)
  have ha := hu (0,a) (epsilonInclusionAt_normalFormAt sY U a)
  have hb := hu (0,b) (hab.trans (epsilonInclusionAt_normalFormAt sY U b))
  exact congrArg Prod.snd (ha.trans hb.symm)

theorem reduction_zero_iff (U : (space sY).Opens) (z : RingSections (space sY) U) :
    (zeroSection sY).app U z = 0 ↔
      ∃ a : RingSections Y (zeroSection sY ⁻¹ᵁ U), epsilonInclusionAt sY U a = z := by
  constructor
  · intro hz
    obtain ⟨⟨a,b⟩, hab, _⟩ := normalFormAt_unique sY U z
    have ha : a = 0 := by
      rw [hab, reduction_normalFormAt] at hz
      exact hz
    refine ⟨b, ?_⟩
    rw [hab, ha, epsilonInclusionAt_normalFormAt]
  · rintro ⟨a, rfl⟩
    rw [epsilonInclusionAt_normalFormAt, reduction_normalFormAt]

theorem epsilonAt_square (U : (space sY).Opens) : (epsilonAt sY U)^2 = 0 := by
  unfold epsilonAt
  rw [← map_pow, ← map_pow, ← map_pow,
    LeBrunSalamon.Construction.Infinitesimal.epsilon_square, map_zero, map_zero, map_zero]

theorem epsilonInclusionAt_scalar (U : (space sY).Opens)
    (r : RingSections (space sY) U) (a : RingSections Y (zeroSection sY ⁻¹ᵁ U)) :
    epsilonInclusionAt sY U ((zeroSection sY).app U r * a) =
      r * epsilonInclusionAt sY U a := by
  obtain ⟨⟨b,c⟩, hr, _⟩ := normalFormAt_unique sY U r
  rw [hr, reduction_normalFormAt]
  simp only [epsilonInclusionAt, normalFormAt, map_mul]
  ring_nf
  simp only [epsilonAt_square, zero_mul, add_zero]

theorem liftRing_restrict {U V : (space sY).Opens} (i : U ⟶ V)
    (a : RingSections Y (zeroSection sY ⁻¹ᵁ V)) :
    (space sY).presheaf.map i.op (liftRing sY V a) =
      liftRing sY U (Y.presheaf.map
        (((TopologicalSpace.Opens.map (zeroSection sY).base).map i).op) a) := by
  have h : Y.presheaf.map
      (((TopologicalSpace.Opens.map (zeroSection sY).base).map i).op) ≫ liftRing sY U =
      liftRing sY V ≫ (space sY).presheaf.map i.op := by
    unfold liftRing
    rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
  exact (congrArg (fun k => k a) h).symm

theorem epsilonAt_restrict {U V : (space sY).Opens} (i : U ⟶ V) :
    (space sY).presheaf.map i.op (epsilonAt sY V) = epsilonAt sY U := by
  unfold epsilonAt
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem epsilonInclusionAt_restrict {U V : (space sY).Opens} (i : U ⟶ V)
    (a : RingSections Y (zeroSection sY ⁻¹ᵁ V)) :
    (space sY).presheaf.map i.op (epsilonInclusionAt sY V a) =
      epsilonInclusionAt sY U (Y.presheaf.map
        (((TopologicalSpace.Opens.map (zeroSection sY).base).map i).op) a) := by
  simp only [epsilonInclusionAt, map_mul, epsilonAt_restrict, liftRing_restrict]

/-- The actual O-module epsilon inclusion. Its linearity uses reduction
on scalars, exactly as required by the zero-section pushforward. -/
def epsilonInjection :
    (Scheme.Modules.pushforward (zeroSection sY)).obj (structureModule Y) ⟶
      structureModule (space sY) where
  val :=
    { app := fun U => ModuleCat.ofHom
        (X := (((Scheme.Modules.pushforward (zeroSection sY)).obj
          (structureModule Y)).val.obj U))
        (Y := ((structureModule (space sY)).val.obj U))
        { toFun := epsilonInclusionAt sY U.unop
          map_add' := by
            intro a b
            simp only [epsilonInclusionAt, map_add, mul_add]
          map_smul' := by
            intro r a
            change RingSections (space sY) U.unop at r
            change RingSections Y (zeroSection sY ⁻¹ᵁ U.unop) at a
            change epsilonInclusionAt sY U.unop ((zeroSection sY).app U.unop r * a) =
              r * epsilonInclusionAt sY U.unop a
            exact epsilonInclusionAt_scalar sY U.unop r a }
      naturality := by
        intro U V i
        ext a
        exact (epsilonInclusionAt_restrict sY i.unop a).symm }

theorem epsilonInjection_reduction :
    epsilonInjection sY ≫ structurePushforwardMap (zeroSection sY) = 0 := by
  apply Scheme.Modules.hom_ext
  intro U
  ext a
  change (zeroSection sY).app U (epsilonInclusionAt sY U a) = 0
  rw [epsilonInclusionAt_normalFormAt, reduction_normalFormAt]

/-- The epsilon sequence is short exact on all actual opens, hence is
short exact in the original category of module sheaves. -/
theorem epsilon_structure_shortExact :
    (ShortComplex.mk (epsilonInjection sY) (structurePushforwardMap (zeroSection sY))
      (epsilonInjection_reduction sY)).ShortExact := by
  apply SheafSectionExact.shortExact_of_sections
  · intro U
    exact epsilonInclusionAt_injective sY U
  · intro U a
    exact ⟨liftRing sY U a, reduction_liftRing sY U a⟩
  · intro U z
    exact reduction_zero_iff sY U z

end LeBrunSalamon.DualHomVanishing
end
