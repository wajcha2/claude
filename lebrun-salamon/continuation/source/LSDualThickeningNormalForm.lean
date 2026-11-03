import LSFiniteFreeBaseChange
import LSDualBaseChangeAlgebra

/-!
# Functions on every open of the actual trivial dual-number thickening

The finite free base-change theorem is applied to the inverse-image open
itself.  The proof then transports the actual pullback maps through the
canonical open-restriction isomorphisms, preserving the original epsilon.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 300000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.Construction
open scoped TensorProduct

namespace LeBrunSalamon.DualBaseChangeAlgebra

open Infinitesimal

instance dual_finite : Module.Finite ℂ Dual :=
  Module.Finite.of_surjective dualCoefficients.symm.toLinearMap
    dualCoefficients.symm.surjective

theorem global_normalForm_unique {X Y : Scheme} (sX : X ⟶ ComplexBase)
    (p : Y ⟶ X) (q : Y ⟶ DualScheme)
    (h : IsPullback p q sX dualToC) (z : Γ(Y, ⊤)) :
    ∃! ab : Γ(X, ⊤) × Γ(X, ⊤),
      z = p.appTop ab.1 +
        q.appTop ((Scheme.ΓSpecIso (CommRingCat.of Dual)).inv epsilon) *
          p.appTop ab.2 := by
  letI := FiniteFreeBaseChange.sectionAlgebra ℂ sX
  let f := FiniteFreeBaseChange.globalMap ℂ Dual sX p q h.w
  have hf : Function.Bijective f :=
    PublishedInputs.FiniteFreeBaseChange.structureH0_bijective ℂ Dual sX p q h
  obtain ⟨w, hw⟩ := hf.2 z
  obtain ⟨ab, hab, huniq⟩ := tensor_normalForm Γ(X, ⊤) w
  have hnf (a b : Γ(X, ⊤)) :
      f (a ⊗ₜ[ℂ] (1 : Dual) + b ⊗ₜ[ℂ] epsilon) =
        p.appTop a +
          q.appTop ((Scheme.ΓSpecIso (CommRingCat.of Dual)).inv epsilon) *
            p.appTop b := by
    simp only [f, map_add, FiniteFreeBaseChange.globalMap_tmul, map_one, mul_one]
    rw [mul_comm (p.appTop b)]
  refine ⟨ab, ?_, ?_⟩
  · rw [← hw, hab, hnf]
  · intro cd hcd
    apply huniq cd
    apply hf.1
    rw [hw, hnf]
    exact hcd

theorem open_normalForm_unique {X Y : Scheme} (sX : X ⟶ ComplexBase)
    (p : Y ⟶ X) (q : Y ⟶ DualScheme)
    (h : IsPullback p q sX dualToC) (U : X.Opens)
    (z : Γ(Y, p ⁻¹ᵁ U)) :
    ∃! ab : Γ(X, U) × Γ(X, U),
      z = p.app U ab.1 +
        Y.presheaf.map (homOfLE (show p ⁻¹ᵁ U ≤ ⊤ from le_top)).op
          (q.appTop ((Scheme.ΓSpecIso (CommRingCat.of Dual)).inv epsilon)) *
            p.app U ab.2 := by
  let V : Y.Opens := p ⁻¹ᵁ U
  let pU : V.toScheme ⟶ U.toScheme := p.resLE U V le_rfl
  let qU : V.toScheme ⟶ DualScheme := V.ι ≫ q
  have hU : IsPullback pU qU (U.ι ≫ sX) dualToC := by
    dsimp [pU, qU, V]
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact (isPullback_morphismRestrict p U).paste_vert h
  have hp (a : Γ(X, U)) : pU.appTop (U.topIso.inv a) = V.topIso.inv (p.app U a) := by
    change (p.resLE U V le_rfl).app ⊤ (U.topIso.inv a) = _
    rw [Scheme.Hom.resLE_app_top, Scheme.Hom.appLE_eq_app]
    change V.topIso.inv (p.app U (U.topIso.hom (U.topIso.inv a))) = _
    rw [Iso.inv_hom_id_apply]
  have hq : qU.appTop ((Scheme.ΓSpecIso (CommRingCat.of Dual)).inv epsilon) =
      V.topIso.inv (Y.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
        (q.appTop ((Scheme.ΓSpecIso (CommRingCat.of Dual)).inv epsilon))) := by
    rw [ScalarSections.topIso_inv_restrict]
    rfl
  obtain ⟨ab, hab, huniq⟩ := global_normalForm_unique (U.ι ≫ sX) pU qU hU
    (V.topIso.inv z)
  refine ⟨(U.topIso.hom ab.1, U.topIso.hom ab.2), ?_, ?_⟩
  · apply (ConcreteCategory.bijective_of_isIso V.topIso.inv).1
    rw [map_add, map_mul, ← hp, ← hp, ← hq]
    simpa only [Iso.hom_inv_id_apply] using hab
  · intro cd hcd
    have hcd' : V.topIso.inv z =
        pU.appTop (U.topIso.inv cd.1) +
          qU.appTop ((Scheme.ΓSpecIso (CommRingCat.of Dual)).inv epsilon) *
            pU.appTop (U.topIso.inv cd.2) := by
      rw [hcd, map_add, map_mul, ← hp, ← hp, ← hq]
    have he := huniq (U.topIso.inv cd.1, U.topIso.inv cd.2) hcd'
    apply Prod.ext
    · exact (Iso.inv_hom_id_apply U.topIso cd.1).symm.trans
        (congrArg (fun a => U.topIso.hom a) (congrArg Prod.fst he))
    · exact (Iso.inv_hom_id_apply U.topIso cd.2).symm.trans
        (congrArg (fun a => U.topIso.hom a) (congrArg Prod.snd he))

end LeBrunSalamon.DualBaseChangeAlgebra

end
